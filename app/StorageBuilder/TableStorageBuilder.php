<?php

namespace App\StorageBuilder;

use Illuminate\Support\Facades\DB;
use App\RuntimeStorage;

class TableStorageBuilder implements Builder
{

    static function build($runtime, $key, $payload)
    {
        $table = 'cceg_runtime_'.$runtime->id.'.'.$key;

        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->type = 'table';
        $storage->state = 'init';
        $storage->payload = [
            'table' => $table,
            'schema' => $payload['schema']
        ];

        $storage->save();

        $columns = collect($payload['schema'])->map(function($column) {
            return $column['name'] . ' ' . $column['type'] . ' NULL';
        })->implode(',');

        DB::statement("CREATE TABLE $table ($columns)");

        return $storage;
    }
}