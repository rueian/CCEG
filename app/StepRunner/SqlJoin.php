<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 output table 的 schema 為兩張 join table 組合，欄位前面都加上原 table_
class SqlJoin implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL 連接另一張表 (Join)';
    }

    static function getFormUISchema()
    {
        return [
            'param' => [
                'conditions' => [
                    'items' => [
                        'left' => [
                            'ui:widget' => 'columnSelector',
                            'ui:options' => [
                                'inputKey' => 'left'
                            ]
                        ],
                        'right' => [
                            'ui:widget' => 'columnSelector',
                            'ui:options' => [
                                'inputKey' => 'right'
                            ]
                        ],
                    ]
                ]
            ]
        ];
    }

    static function getFormSchema($bluePrintStorages)
    {
        $inputKeys = [];
        $inputNames = [];
        foreach ($bluePrintStorages as $key => $storage) {
            if ($storage['type'] == static::supportedInputStorageType()) {
                $inputKeys[] = $key;
                $inputNames[] = $storage['name'] . ' (' . $key . ')';
            }
        }

        return [
            'type' => 'object',
            'required' => [
                'name',
                'inputs',
                'param'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '步驟名稱'
                ],
                'note' => [
                    'type' => 'string',
                    'title' => '步驟備註'
                ],
                'inputs' => [
                    'type' => 'object',
                    'title' => '選擇輸入儲存空間',
                    'required' => [
                        'left',
                        'right'
                    ],
                    'properties' => [
                        'left' => [
                            'title' => '左方儲存空間',
                            'type' => 'string',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ],
                        'right' => [
                            'title' => '右方儲存空間',
                            'type' => 'string',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ]
                    ]
                ],
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'required' => [
                        'method',
                    ],
                    'properties' => [
                        'method' => [
                            'title' => 'Join 方法',
                            'type' => 'string',
                            'enum' => [
                                'LEFT JOIN',
                                'INNER JOIN'
                            ],
                            'default' => 'LEFT JOIN'
                        ],
                        'conditions' => [
                            'title' => 'Join 條件，多個用 AND 串接',
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'properties' => [
                                    'left' => [
                                        'title' => '左方儲存空間的欄位',
                                        'type' => 'string',
                                    ],
                                    'operator' => [
                                        'title' => '運算子',
                                        'type' => 'string',
                                        'enum' => [
                                            '=',
                                            '>',
                                            '>=',
                                            '<',
                                            '<='
                                        ],
                                        'default' => '='
                                    ],
                                    'right' => [
                                        'title' => '右方儲存空間的欄位',
                                        'type' => 'string'
                                    ],
                                ]
                            ]
                        ]
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

        if (isset($step->param['conditions'])) {
            $joinCondition = collect($step->param['conditions'])->map(function($condition) use ($leftTable, $rightTable) {
                $leftColumn = $condition['left'];
                $rightColumn = $condition['right'];
                $operator = $condition['operator'];
                return "$leftTable.$leftColumn $operator $rightTable.$rightColumn";
            })->implode(' AND ');

            $joinCondition = "ON ($joinCondition)";
        } else {
            $joinCondition = "";
        }

        $joinMethod = $step->param['method'];

        $query = "INSERT INTO $outputTable ($outputColumns) SELECT $selectColumns FROM $leftTable $joinMethod $rightTable $joinCondition";
        
        DB::statement($query);
    }
}