<?php

namespace App\StorageBuilder;

use Illuminate\Support\Facades\DB;
use App\RuntimeStorage;

class TableStorageBuilder implements Builder
{
    static function getName()
    {
        return 'SQL Table';
    }

    static function getFormUISchema()
    {
        return [
            'schema' => [
                'items' => [
                    'ui:field' => 'columnCreator'
                ]
            ]
        ];
    }

    static function getFormSchema()
    {
        return [
            'type' => 'object',
            'required' => [
                'name',
                'schema'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '儲存空間名稱(限英數字與底線的組合)',
                ],
                'schema' => [
                    'type' => 'array',
                    'title' => '選擇欄位',
                    'items' => [
                        'type' => 'object',
                        'required' => [
                            'name',
                            'type'
                        ],
                        'properties' => [
                            'name' => [
                                'type' => 'string',
                                'title' => '欄位名稱(限英數字與底線的組合)'
                            ],
                            'type' => [
                                'type' => 'string',
                                'title' => '欄位型別',
                                'enum' => [
                                    'integer',
                                    'float',
                                    'varchar(255)',
                                ],
                                'enumNames' => [
                                    '整數 (integer)',
                                    '浮點數 (float)',
                                    '字串 (varchar(255))',
                                ]
                            ],
                        ]
                    ],
                ],
            ]
        ];
    }

    static function build($runtime, $key, $name, $payload)
    {
        $table = 'cceg_runtime_'.$runtime->id.'.'.$key;

        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->name = $name;
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