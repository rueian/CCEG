<?php

namespace App;

use App\StorageBuilder\SmtVariableTableStorageBuilder;
use App\StorageBuilder\TableStorageBuilder;
use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;

/**
 * App\RuntimeStorage
 *
 * @property int $id
 * @property int $runtime_id
 * @property string $key
 * @property string $name
 * @property string $type
 * @property array $payload
 * @property string $state
 * @property mixed|null $error
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\StepConnection[] $connections
 * @property-read \App\Runtime $runtime
 * @mixin \Eloquent
 */
class RuntimeStorage extends Model
{
    public static $builderMap = [
        'table' => TableStorageBuilder::class,
        'smt_variable_table' => SmtVariableTableStorageBuilder::class,
    ];

    public static $userCreatable = ['table', 'smt_variable_table'];

    protected $guarded = [];

    protected $casts = [
        'payload' => 'array',
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

    public function cleanStorage()
    {
        if ($this->type == 'table') {
            DB::statement('DELETE FROM ' . $this->payload['table']);
        }
    }

    public function import($data)
    {
        if ($this->type == 'table') {
            $header = $data[0];

            $rows = [];
            for ($i = 1; $i < count($data); $i++) {
                $d = [];
                for ($j = 0; $j < count($data[$i]); $j++) {
                    if ($this->payload['schema'][$j]['type'] == 'varchar(255)') {
                        $d[] = '"' . $data[$i][$j] . '"';
                    } else {
                        $d[] = strlen($data[$i][$j]) > 0 ? $data[$i][$j] : 'NULL';
                    }
                }
                $rows[] = implode($d, ',');
            }

            DB::statement('INSERT INTO ' . $this->payload['table'] . '(' . implode($header, ',') . ') VALUES (' . implode($rows, '),(') . ')');

            return;
        }

        if ($this->type == 'smt_input') {
            $payload = $this->payload;
            $payload['content'] = $data;
            $this->payload = $payload;
            $this->save();
            return;
        }
    }

    public function export()
    {
        if ($this->type == 'table') {
            $rows = DB::table($this->payload['table'])->select('*')->get();

            $headers = [];
            foreach ($this->payload['schema'] as $column) {
                $headers[] = $column['name'];
            }

            $data = [];
            $data[] = $headers;

            foreach ($rows as $row) {
                $r = [];
                foreach ($headers as $h) {
                    $r[] = $row->$h;
                }
                $data[] = $r;
            }

            return $data;
        }

        if ($this->type == 'smt_input' || $this->type == 'smt_output') {
            return $this->payload['content'];
        }

        return [];
    }

    static public function getAllFormSchema()
    {
        $formSchemaMap = [];

        foreach (static::$builderMap as $type => $builder) {
            $formSchemaMap[$type] = [
                'schema' => $builder::getFormSchema(),
                'uiSchema' => $builder::getFormUISchema(),
                'name' => $builder::getName(),
                'userCreatable' => in_array($type, static::$userCreatable)
            ];
        }

        return $formSchemaMap;
    }

    /**
     * @param $runtime
     * @param $key
     * @param $type
     * @param $payload
     * @return RuntimeStorage
     * @throws \Exception
     */
    static public function createStorage($runtime, $key, $type, $name, $payload)
    {
        $builder = static::$builderMap[$type];
        if (!$builder) {
            throw new \Exception('Un supported storage type: '.$type);
        }

        return $builder::build($runtime, $key, $name, $payload);
    }

    static public function createTableStorage($runtime, $key, $name, $schema)
    {
        return TableStorageBuilder::build($runtime, $key, $name, [
            'schema' => $schema
        ]);
    }

    static public function createSmtVariableTableStorage($runtime, $key, $name)
    {
        return SmtVariableTableStorageBuilder::build($runtime, $key, $name, []);
    }
}
