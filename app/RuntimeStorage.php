<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;

class RuntimeStorage extends Model
{
    protected $guarded = [];

    protected $casts = [
        'payload' => 'array'
    ];

    public function runtime()
    {
        return $this->belongsTo('App\Runtime');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }

    public function supportedOperation()
    {
        if ($this->type == 'table') {

        } else {

        }
    }

    static public function createSMTInputStorage($runtime, $key, $content)
    {
        return static::createSMTStorage('smt_input', $runtime, $key, $content);
    }

    static public function createSMTOutputStorage($runtime, $key, $content)
    {
        return static::createSMTStorage('smt_output', $runtime, $key, $content);
    }

    static public function createSMTStorage($type, $runtime, $key, $content)
    {
        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->type = $type;
        $storage->state = 'init';
        $storage->payload = [
            'content' => $content
        ];

        $storage->save();

        return $storage;
    }

    static public function createTableStorage($runtime, $key, $table, $schema)
    {
        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->type = 'table';
        $storage->state = 'init';
        $storage->payload = [
            'table' => $table,
            'schema' => $schema
        ];

        $storage->save();

        $columns = $schema->map(function($column) {
            return $column['name'] . ' ' . $column['type'] . ' NULL';
        })->implode(',');

        DB::statement("CREATE TABLE $table ($columns)");

        return $storage;
    }
}
