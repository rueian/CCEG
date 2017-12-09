<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;

use App\StepConnection;

class Step extends Model
{
    public static $runnerMap = [
        'sql_filter_by_condition' => StepRunner\SqlFilterByCondition::class,
        'sql_filter_by_semi_join' => StepRunner\SqlFilterBySemiJoin::class,
        'sql_left_join'           => StepRunner\SqlLeftJoin::class,
        'sql_order_by'            => StepRunner\SqlOrderBy::class,
        'sql_limit_offset'        => StepRunner\SqlLimitOffset::class,
        'sql_group_by'            => StepRunner\SqlGroupBy::class,
        'sql_select_map'          => StepRunner\SqlSelectMap::class,
        'smt'                     => StepRunner\Smt::class,
        'smt_output_to_table'     => StepRunner\SmtOutputToTable::class
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
        $step->state = 'ready';
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
}
