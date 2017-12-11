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