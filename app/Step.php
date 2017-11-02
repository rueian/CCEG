<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;

use App\StepConnection;

class Step extends Model
{
    protected $guarded = [];

    protected $casts = [
        'param' => 'array',
        'error' => 'array'
    ];

    public function runtime()
    {
        return $this->belongsTo('App\Runtime');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }

    public function run()
    {
        $conns = $this->connections;
        $conns->load('storage');

        $input = $conns->first(function($c) {
            return $c->type == 'input';
        });

        $output = $conns->first(function($c) {
            return $c->type == 'output';
        });

        if ($this->type == 'sql') {
            $inputTable = $input->storage->payload['table'];
            $outputTable = $output->storage->payload['table'];

            $selects = collect($this->param['selects'])->pluck('select')->implode(',');
            $columns = collect($this->param['selects'])->pluck('rename')->implode(',');

            $query = "INSERT INTO $outputTable ($columns) SELECT $selects FROM $inputTable";

            if (isset($this->param['where'])) {
                $query = $query . ' WHERE ' . $this->param['where'];
            }

            if (isset($this->param['group'])) {
                $query = $query . ' GROUP BY ' . $this->param['group'];
            }

            if (isset($this->param['having'])) {
                $query = $query . ' HAVING ' . $this->param['having'];
            }

            if (isset($this->param['order'])) {
                $query = $query . ' ORDER BY ' . $this->param['order'];
            }

            if (isset($this->param['limit'])) {
                $query = $query . ' LIMIT ' . $this->param['limit'];
            }

            if (isset($this->param['offset'])) {
                $query = $query . ' OFFSET ' . $this->param['offset'];
            }

            DB::statement($query);
            return;
        }

        if ($this->type == 'smt') {
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

    static public function createSMTStep($runtime, $name, $note, $input, $output, $param)
    {
        return static::createStep('smt', $runtime, $name, $note, $input, $output, $param);
    }

    static public function createSQLStep($runtime, $name, $note, $input, $output, $param)
    {
        return static::createStep('sql', $runtime, $name, $note, $input, $output, $param);
    }

    static public function createStep($type, $runtime, $name, $note, $input, $output, $param)
    {
        $step = new Step;
        $step->runtime_id = $runtime->id;
        $step->name = $name;
        $step->note = $note;
        $step->type = $type;
        $step->param = $param;
        $step->state = 'ready';
        $step->save();

        $connInput = new StepConnection;
        $connOutput = new StepConnection;

        $connInput->runtime_id = $runtime->id;
        $connInput->runtime_storage_id = $input->id;
        $connInput->step_id = $step->id;
        $connInput->type = 'input';
        $connInput->save();

        $connOutput->runtime_id = $runtime->id;
        $connOutput->runtime_storage_id = $output->id;
        $connOutput->step_id = $step->id;
        $connOutput->type = 'output';
        $connOutput->save();

        return $step;
    }
}
