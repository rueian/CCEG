<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

class Smt implements Runner
{
    static function supportedInputStorageType()
    {
        return 'smt_variable_table';
    }

    static function getName()
    {
        return 'SMT';
    }

    static function getFormUISchema()
    {
        return [
            'param' => [
                'content' => [
                    'ui:widget' => 'textarea'
                ],
                'varList' => [
                    'items' => [
                        'ui:field' => 'columnCreator'
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
                'inputs'
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
                'param' => [
                    'type' => 'object',
                    'title' => '步驟參數',
                    'properties' => [
                        'varList' => [
                            'title' => '定義變數',
                            'type' => 'array',
                            'items' => [
                                'type' => 'object',
                                'required' => [
                                    'name',
                                    'type'
                                ],
                                'properties' => [
                                    'name' => [
                                        'title' => '變數名稱',
                                        'type' => 'string',
                                    ],
                                    'type' => [
                                        'title' => '變數型別',
                                        'type' => 'string',
                                        'enum' => [
                                            'Real',
                                        ],
                                        'enumNames' => [
                                            'Real'
                                        ],
                                        'default' => 'Real'
                                    ]
                                ]
                            ]
                        ],
                        'content' => [
                            'type' => 'string',
                            'title' => 'SMT 內容'
                        ],
                    ]
                ],
                'inputs' => [
                    'type' => 'object',
                    'title' => '選擇輸入資料源',
                    'required' => [
                        'input'
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
            ]
        ];
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        return [
            'type' => 'smt_variable_table',
            'schema' => [
                [
                    'name' => 'variable',
                    'type' => 'varchar(255)'
                ],
                [
                    'name' => 'value',
                    'type' => 'varchar(255)'
                ]
            ]
        ];
    }

    static function generateSmtInput($varTableName, $stepParam)
    {
        $inputContent = '';

        $VarNameTypeMap = [];
        foreach($stepParam['varList'] as $v) {
            $VarNameTypeMap[$v['name']] = $v['type'];
        }
        foreach($VarNameTypeMap as $name => $type) {
            $inputContent .= "(declare-const $name $type)\n";
        }

        $variables = DB::table($varTableName)->get();
        $VarNameValueMap = [];
        foreach($variables as $v) {
            $VarNameValueMap[$v->variable] = $v->value;
        }
        foreach($VarNameValueMap as $name => $value) {
            if (strlen($value) > 0 && array_key_exists($name, $VarNameTypeMap)) {
                $inputContent .= "(assert (= $name $value))\n";
            }
        }

        $inputContent .= $stepParam['content'] . "\n";
        $inputContent .= "(check-sat)\n";

        foreach(array_keys($VarNameTypeMap) as $v) {
            $inputContent .= "(get-value ($v))\n";
        }

        return $inputContent;
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
        $param = $step->param;

        $param['input'] = static::generateSmtInput($inputTable, $param);
        $step->param = $param;
        $step->save();

        $descriptorspec = [
            ['pipe', 'r'],  // stdin is a pipe that the child will read from
            ['pipe', 'w'],  // stdout is a pipe that the child will write to
            ['pipe', 'w']   // stderr is a pipe that the child will write to
        ];

        $z3Path = base_path('z3');
        $process = proc_open("$z3Path -smt2 -in 2>&1", $descriptorspec, $pipes, '/tmp', []);
        if (is_resource($process)) {
            fwrite($pipes[0], $param['input']);
            fclose($pipes[0]);

            $out = stream_get_contents($pipes[1]);
            fclose($pipes[1]);
            fclose($pipes[2]);

            $returnValue = proc_close($process);

            $param['output'] = $out;
            $step->param = $param;
            $step->save();

            if ($returnValue != 0) {
                throw new \Exception($out);
            } else {
                // translate SMT (get-value into table row)
                $lines = explode("\n", trim($out));

                if (count($lines) > 1) {
                    if ($lines[0] != "sat") {
                        throw \Exception("smt model is not available");
                    }

                    $outputTable = $output->storage->payload['table'];

                    $query = "INSERT INTO $outputTable (variable, value) VALUES ";

                    $values = [];
                    for($i = 1; $i < count($lines); $i++) {
                        preg_match('/\(\(([a-z]*) (.*)\)\)/', $lines[$i], $matches);
                        $k = $matches[1];
                        $v = $matches[2];
                        $values[] = "('$k', $v)";
                    }
                    $query .= implode(', ', $values);
                    DB::statement($query);
                }
            }
        }
        return;
    }
}