<?php

namespace App\StepRunner;

use Illuminate\Support\Facades\DB;

class SmtOutputToTable implements Runner
{
    static function supportedInputStorageType()
    {
        return 'smt_output';
    }

    static function getName()
    {
        return 'SMT 輸出轉成 SQL 表格';
    }

    static function getBlueprintStepStorage($bluePrintStorages, $bluePrintStepPayload)
    {
        return [
            'type' => 'smt_result',
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
                'key',
                'inputs'
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

    static function run($step)
    {
        $input = $step->connections->first(function($c) {
            return $c->type == 'input';
        });

        $output = $step->connections->first(function($c) {
            return $c->type == 'output';
        });

        // translate SMT (get-value into table row)
        $inputContent = $input->storage->payload['content'];
        $lines = explode("\n", trim($inputContent));

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
        return;
    }
}