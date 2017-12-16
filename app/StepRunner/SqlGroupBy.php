<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 output table 的必須 select 完全一樣
class SqlGroupBy implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL 聚合運算 (Group By)';
    }

    static function getFormUISchema()
    {
        return [
            'param' => [
                'group' => [
                    'items' => [
                        'ui:widget' => 'columnSelector',
                        'ui:options' => [
                            'inputKey' => 'input'
                        ]
                    ]
                ],
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
                    'title' => '選擇輸入資料源',
                    'required' => [
                        'input',
                    ],
                    'properties' => [
                        'input' => [
                            'title' => '輸入資料源',
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
                        'group',
                    ],
                    'properties' => [
                        'group' => [
                            'title' => 'GROUP BY 欄位',
                            'type' => 'array',
                            'items' => [
                                'type' => 'string'
                            ]
                        ],
                        'select' => [
                            'title' => '額外 SELECT 欄位',
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'expr',
                                    'as',
                                    'type'
                                ],
                                'properties' => [
                                    'expr' => [
                                        'title' => '來源欄位名稱或 SQL 表達式',
                                        'type' => 'string'
                                    ],
                                    'as' => [
                                        'title' => '輸出欄位名稱',
                                        'type' => 'string'
                                    ],
                                    'type' => [
                                        'title' => '欄位型別',
                                        'type' => 'string',
                                        'enum' => [
                                            'integer',
                                            'float',
                                            'double',
                                            'varchar',
                                        ],
                                        'enumNames' => [
                                            '整數 (integer)',
                                            '浮點數 (float)',
                                            '雙精度 (double)',
                                            '字串 (varchar)',
                                        ]
                                    ]
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
        $inputStorage = $bluePrintStorages[$bluePrintStepPayload['inputs']['input']];

        $targetSchema = collect();
        foreach($bluePrintStepPayload['param']['select'] as $selectedColumn) {
            $targetSchema->push([
                'name' => $selectedColumn['as'],
                'type' => $selectedColumn['type'],
            ]);
        }
        foreach($bluePrintStepPayload['param']['group'] as $groupedColumn) {
            foreach($inputStorage['schema'] as $inputColumn) {
                if ($inputColumn['name'] == $groupedColumn) {
                    if ($targetSchema->contains(function($column) use ($groupedColumn) {
                        return $column['name'] == $groupedColumn;
                    })) {
                        continue;
                    }
                    $targetSchema->push([
                        'name' => $inputColumn['name'],
                        'type' => $inputColumn['type'],
                    ]);
                }
            }
        }

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

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $inputTable = $input->storage->payload['table'];
        $outputTable = $output->storage->payload['table'];

        // [
        //     'group' => [
        //         'xxx',
        //         'yyy'
        //     ],
        //     'select' => [
        //         [
        //             'expr' => 'max(xxx)',
        //             'as' => 'max_xxx',
        //             'type' => 'integer',
        //         ],
        //     ]
        // ]

        $outputColumns = collect();
        $selectColumns = collect();

        foreach($step->param['select'] as $column) {
            $outputColumns->push($column['as']);
            $selectColumns->push($column['expr']);
        }

        foreach ($step->param['group'] as $columnName) {
            if ($outputColumns->contains($columnName)) {
                continue;
            }
            $outputColumns->push($columnName);
            $selectColumns->push($columnName);
        }

        $outputColumns = $outputColumns->implode(',');
        $selectColumns = $selectColumns->implode(',');

        $groupBy = collect($step->param['group'])->implode(',');

        $query = "INSERT INTO $outputTable ($outputColumns) SELECT $selectColumns FROM $inputTable GROUP BY $groupBy";

        DB::statement($query);
    }
}