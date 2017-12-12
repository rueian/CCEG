<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 output table 的 schema 為兩張 join table 組合，欄位前面都加上原 table_
class SqlLeftJoin implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL Join 連接另一張表';
    }

    static function getFormSchema($bluePrintStorages)
    {
        $inputKeys = [];
        foreach ($bluePrintStorages as $key => $storage) {
            if ($storage['type'] == static::supportedInputStorageType()) {
                $inputKeys[] = $key;
            }
        }

        return [
            'type' => 'object',
            'required' => [
                'name',
                'key',
                'inputs',
                'param'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '步驟名稱'
                ],
                'key' => [
                    'type' => 'string',
                    'title' => '步驟代號'
                ],
                'note' => [
                    'type' => 'string',
                    'title' => '步驟備註'
                ],
                'inputs' => [
                    'type' => 'object',
                    'title' => '選擇輸入資料源',
                    'required' => [
                        'left',
                        'right'
                    ],
                    'properties' => [
                        'left' => [
                            'type' => 'string',
                            'enum' => $inputKeys
                        ],
                        'right' => [
                            'type' => 'string',
                            'enum' => $inputKeys
                        ]
                    ]
                ],
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'required' => [
                        'left',
                        'right',
                    ],
                    'properties' => [
                        'left' => [
                            'type' => 'string',
                        ],
                        'right' => [
                            'type' => 'string'
                        ],
                    ]
                ],
            ]
        ];
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        $leftTable = $bluePrintStepPayload['inputs']['left'];
        $rightTable = $bluePrintStepPayload['inputs']['right'];
        $leftSchema = $bluePrintStorages[$leftTable]['schema'];
        $rightSchema = $bluePrintStorages[$rightTable]['schema'];

        $targetSchema = [];

        foreach($leftSchema as $column) {
            $targetSchema[] = [
                'name' => $leftTable.'_'.$column['name'],
                'type' => $column['type']
            ];
        }

        foreach($rightSchema as $column) {
            $targetSchema[] = [
                'name' => $rightTable.'_'.$column['name'],
                'type' => $column['type']
            ];
        }

        return [
            'type' => 'table',
            'schema' => $targetSchema
        ];
    }

    static function run($step)
    {
        $left = $step->connections->first(function($c) {
            return $c->type == 'left';
        });

        $right = $step->connections->first(function($c) {
            return $c->type == 'right';
        });

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $leftTable = $left->storage->payload['table'];
        $rightTable = $right->storage->payload['table'];
        $outputTable = $output->storage->payload['table'];

        $outputColumns = collect();
        $selectColumns = collect();

        foreach($left->storage->payload['schema'] as $column) {
            $outputColumns->push($left->storage->key.'_'.$column['name']);
            $selectColumns->push($left->storage->key.'.'.$column['name']);
        }

        foreach($right->storage->payload['schema'] as $column) {
            $outputColumns->push($right->storage->key.'_'.$column['name']);
            $selectColumns->push($right->storage->key.'.'.$column['name']);
        }

        $outputColumns = $outputColumns->implode(',');
        $selectColumns = $selectColumns->implode(',');

//        [
//            'left' => 'xxx',
//            'right' => 'yyy'
//        ]

        $leftColumn = $step->param['join']['left'];
        $rightColumn = $step->param['join']['right'];

        $query = "INSERT INTO $outputTable ($outputColumns) SELECT $selectColumns FROM $leftTable LEFT JOIN $rightTable ON $leftTable.$leftColumn = $rightTable.$rightColumn";
        
        DB::statement($query);
    }
}