<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;

use App\Blueprint;
use App\Step;
use App\StepConnection;
use App\RuntimeStorage;

class Runtime extends Model
{
    protected $guarded = [];

    protected $casts = [
        'error' => 'array'
    ];

    public function blueprint()
    {
        return $this->belongsTo('App\Blueprint');
    }

    public function storages()
    {
        return $this->hasMany('App\RuntimeStorage');
    }

    public function steps()
    {
        return $this->hasMany('App\Step');
    }

    public function connections()
    {
        return $this->hasMany('App\StepConnection');
    }

    public function getStepSequence()
    {
        $storages = $this->storages;
        $steps = $this->steps;
        $connections = $this->connections;

        // remap storages and steps into a list identified by its index
        $nodes = collect();
        $storageMap = [];
        $stepMap = [];

        foreach($storages as $storage) {
            $storageMap[$storage->id] = $nodes->count();
            $nodes->push(new Node($storage));
        }

        foreach($steps as $step) {
            $stepMap[$step->id] = $nodes->count();
            $nodes->push(new Node($step));
        }

        // build the Adjacency lists and refs count
        foreach($connections as $conn) {
            $stepNode = $nodes[$stepMap[$conn->step_id]];
            $storageNode = $nodes[$storageMap[$conn->runtime_storage_id]];

            if ($conn->type == 'input') {
                $storageNode->adj_list->push($stepNode);
                $stepNode->refed_count++;
            } else {
                $stepNode->adj_list->push($storageNode);
                $storageNode->refed_count++;
            }
        }

        // Topological Ordering - Kahn's Algorithm
        $candidates = $nodes->filter(function($n) {
            return $n->refed_count == 0;
        });

        $result = collect();
        foreach($nodes as $n) {
            if ($candidates->isEmpty()) break;

            $c = $candidates->pop();

            if ($c->v instanceof Step) {
                $result->push($c->v);
            }

            foreach($c->adj_list as $a) {
                $a->refed_count--;
                if ($a->refed_count == 0) {
                    $candidates->push($a);
                }
            }
        }

        return $result;
    }

    public function runOneStep()
    {
        $steps = $this->getStepSequence();

        foreach($steps as $s) {
            if ($s->state == 'ready' || $s->state == 'error') {
                DB::beginTransaction();
                try {
                    $s->run();
                    $s->state = 'done';
                    $s->save();
                    DB::commit();
                } catch (\Exception $e) {
                    Log::error('runOneStep failed: ' . $e->getMessage(), [
                        'runtime_id' => $this->id
                    ]);

                    DB::rollback();

                    $s->state = 'error';
                    $s->error = ['message' => $e->getMessage()];
                    $s->save();

                    $this->state = 'error';
                    $this->error = [
                        'step_id' => $s->id,
                        'message' => $e->getMessage()
                    ];

                    $this->save();

                    throw $e;
                }

                return $s;
            }
        }
    }

    public function dropStorageTables()
    {
        DB::beginTransaction();
        try {
            foreach($this->storages as $storage) {
                if ($storage->type == 'table') {
                    DB::statement('DROP TABLE IF EXISTS ' . $storage->payload['table']);
                }
            }
        } catch (\Exception $e) {
            DB::rollback();
            throw $e;
        }
    }
}

class Node
{
    public $v;
    public $refed_count;
    public $adj_list;

    public function __construct(&$v) {
        $this->v = $v;
        $this->refed_count = 0;
        $this->adj_list = collect();
    }
}