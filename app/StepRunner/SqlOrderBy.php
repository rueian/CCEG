<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

// 此 Runner 的 input table 與 output table 的必須 schema 完全一樣
class SqlOrderBy implements Runner
{
    static function supportedInputStorageType()
    {
        return 'table';
    }

    static function getName()
    {
        return 'SQL 排序 (Order By)';
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
                    ],
                    'properties' => [
                        'input' => [
                            'type' => 'string',
                            'title' => '輸入資料源',
                            'enum' => $inputKeys,
                            'enumNames' => $inputNames
                        ]
                    ]
                ],
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'required' => [
                        'order',
                    ],
                    'properties' => [
                        'order' => [
                            'title' => '選擇排序欄位',
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'column',
                                    'direct'
                                ],
                                'properties' => [
                                    'column' => [
                                        'title' => '欄位',
                                        'type' => 'string',
                                    ],
                                    'direct' => [
                                        'title' => '升冪或降冪',
                                        'type' => 'string',
                                        'enum' => [
                                            'asc',
                                            'desc'
                                        ],
                                        'enumNames' => [
                                            '升冪 (ASC)',
                                            '降冪 (DESC)'
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

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        $inputTable = $input->storage->payload['table'];
        $outputTable = $output->storage->payload['table'];

        // [
        //     'order' => [
        //         [
        //             'column' => 'xxx',
        //             'asc' => true 
        //         ],
        //         [
        //             'column' => 'yyy',
        //             'asc' => false 
        //         ],
        //     ]
        // ]

        $query = "INSERT INTO $outputTable SELECT * FROM $inputTable";
        if (isset($step->param['order'])) {
            $orderBy = collect();
            foreach($step->param['order'] as $s) {
                $column = $s['column'];
                $direct = $s['direct'] == 'asc' ? 'asc' : 'desc';
                $orderBy->push("$column $direct");
            }
            $orderBy = $orderBy->implode(',');
            $query = $query . " order by $orderBy";
        }

        DB::statement($query);
    }
}