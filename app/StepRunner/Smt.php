<?php

namespace App\StepRunner;

class Smt implements Runner
{
    static function supportedInputStorageType()
    {
        return 'smt_input';
    }

    static function getName()
    {
        return 'SMT';
    }

    static function getFormUISchema()
    {
        return [
            'param' => []
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
            'type' => 'smt_output',
            'content' => ''
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

        $inputContent = $input->storage->payload['content'];

        $descriptorspec = [
            ['pipe', 'r'],  // stdin is a pipe that the child will read from
            ['pipe', 'w'],  // stdout is a pipe that the child will write to
            ['pipe', 'w']   // stderr is a pipe that the child will write to
        ];

        $z3Path = base_path('z3');
        $process = proc_open("$z3Path -smt2 -in 2>&1", $descriptorspec, $pipes, '/tmp', []);
        if (is_resource($process)) {
            fwrite($pipes[0], $inputContent);
            fclose($pipes[0]);

            $out = stream_get_contents($pipes[1]);
            fclose($pipes[1]);
            fclose($pipes[2]);

            $returnValue = proc_close($process);

            if ($returnValue != 0) {
                throw new \Exception($out);
            } else {
                $payload = $output->storage->payload;
                $payload['content'] = $out;
                $output->storage->payload = $payload;
                $output->storage->save();
            }
        }
        return;
    }
}