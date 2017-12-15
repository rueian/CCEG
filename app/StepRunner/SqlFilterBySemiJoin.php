<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 input table 與 output table 的必須 schema 完全一樣
class SqlFilterBySemiJoin implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL 用另一張格表篩選';
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
                        'input',
                        'semi'
                    ],
                    'properties' => [
                        'input' => [
                            'title' => '原始資料源',
                            'type' => 'string',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ],
                        'semi' => [
                            'title' => '篩選資料源',
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
                        'column',
                        'in',
                        'select'
                    ],
                    'properties' => [
                        'column' => [
                            'title' => '原始資料源的欄位',
                            'type' => 'string',
                        ],
                        'operation' => [
                            'title' => '篩選條件',
                            'type' => 'string',
                            'enum' => [
                                'in',
                                'not in'
                            ],
                            'enumNames' => [
                                '要包含於 (IN)',
                                '要不包含於 (NOT IN)'
                            ]
                        ],
                        'select' => [
                            'title' => '篩選資料源的欄位',
                            'type' => 'string'
                        ]
                    ]
                ],
            ]
        ];
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        $targetSchema = $bluePrintStorages[$bluePrintStepPayload['inputs']['input']]['schema'];
        return [
            'type' => 'table',
            'schema' => $targetSchema
        ];
    }

    static function run($step)
    {
        $input = $step->connections->first(function($c) {
            return $c->type == 'input';
        });

        $semi = $step->connections->first(function($c) {
            return $c->type == 'semi';
        });

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $inputTable = $input->storage->payload['table'];
        $semiTable = $semi->storage->payload['table'];
        $outputTable = $output->storage->payload['table'];

//        [
//            'column' => 'xxx',
//            'in' => true,
//            'select' => 'yyy',
//        ]

        $query = "INSERT INTO $outputTable SELECT * FROM $inputTable";
        if (isset($step->param['semi'])) {
            $column = $step->param['semi']['column'];
            $select = $step->param['semi']['select'];
            $operation = $step->param['semi']['operation'] == 'in' ? 'in' : 'not in';

            $query = $query . " WHERE $column $operation (SELECT $select FROM $semiTable)";
        }

        DB::statement($query);
    }
}