<?php

namespace App;

use Illuminate\Database\Eloquent\Model;

/**
 * App\Step
 *
 * @property int $id
 * @property int $runtime_id
 * @property string $key
 * @property string|null $name
 * @property string|null $note
 * @property string $type
 * @property array $param
 * @property string $state
 * @property array $error
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\StepConnection[] $connections
 * @property-read \App\Runtime $runtime
 * @mixin \Eloquent
 */
class Step extends Model
{
    public static $runnerMap = [
        'sql_filter_by_condition' => StepRunner\SqlFilterByCondition::class,
        'sql_filter_by_semi_join' => StepRunner\SqlFilterBySemiJoin::class,
        'sql_join'                => StepRunner\SqlJoin::class,
        'sql_order_by'            => StepRunner\SqlOrderBy::class,
        'sql_limit_offset'        => StepRunner\SqlLimitOffset::class,
        'sql_group_by'            => StepRunner\SqlGroupBy::class,
        'sql_select_map'          => StepRunner\SqlSelectMap::class,
        'sql_table_to_smt_table'  => StepRunner\SqlTableToSmtTable::class,
        'smt'                     => StepRunner\Smt::class,
    ];

    protected $guarded = [];

    protected $casts = [
        'param' => 'array',
        'error' => 'array'
    ];

    public function runtime()
    {
        return $this->belongsTo('App\Runtime');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }

    public function getOutputStorage()
    {
        $conn = $this->connections->first(function($c) {
            return $c->type == 'output';
        });

        if (!$conn || !$conn->storage) {
            return null;
        }

        return $conn->storage;
    }

    /**
     * @throws \Exception
     */
    public function run()
    {
        $conns = $this->connections;
        $conns->load('storage');

        $runner = static::$runnerMap[$this->type];

        if (!$runner) {
            throw new \Exception('Un supported step type: '.$this->type);
        }

        $runner::run($this);
    }

    /**
     * @param $runtime
     * @param $key
     * @param $type
     * @param $name
     * @param $note
     * @param $param
     * @param $inputs
     * @param $output
     * @return Step
     * @throws \Exception
     */
    static public function createStep($runtime, $key, $type, $name, $note, $param, $inputs, $output)
    {
        $runner = static::$runnerMap[$type];

        if (!$runner) {
            throw new \Exception('Un supported step type: '.$type);
        }

        $step = new Step;
        $step->runtime_id = $runtime->id;
        $step->key = $key;
        $step->name = $name;
        $step->note = $note;
        $step->type = $type;
        $step->param = $param;
        $step->state = 'init';
        $step->save();

        foreach($inputs as $type => $input) {
            $connInput = new StepConnection;
            $connInput->runtime_id = $runtime->id;
            $connInput->runtime_storage_id = $input->id;
            $connInput->step_id = $step->id;
            $connInput->type = $type;
            $connInput->save();
        }

        $connOutput = new StepConnection;
        $connOutput->runtime_id = $runtime->id;
        $connOutput->runtime_storage_id = $output->id;
        $connOutput->step_id = $step->id;
        $connOutput->type = 'output';
        $connOutput->save();

        return $step;
    }

    static public function getAllFormSchema($blueprintPayload)
    {
        $blueprintStroages = isset($blueprintPayload['storages']) ? $blueprintPayload['storages'] : [];

        $formSchemaMap = [];
        foreach (static::$runnerMap as $type => $runner) {
            foreach ($blueprintStroages as $key => $storage) {
                if ($storage['type'] == $runner::supportedInputStorageType()) {
                    $formSchemaMap[$type] = [
                        'name' => $runner::getName(),
                        'schema' => $runner::getFormSchema($blueprintStroages),
                        'uiSchema' => $runner::getFormUISchema(),
                    ];
                    break;
                }
            }
        }

        return $formSchemaMap;
    }
}
