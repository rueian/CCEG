<?php

namespace App\StepRunner;

class Smt extends Runner
{
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