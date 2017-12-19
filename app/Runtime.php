<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;
use Illuminate\Support\Facades\Log;

/**
 * App\Runtime
 *
 * @property int $id
 * @property int $blueprint_id
 * @property string $state
 * @property array $error
 * @property \Carbon\Carbon|null $created_at
 * @property \Carbon\Carbon|null $updated_at
 * @property-read \App\Blueprint $blueprint
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\StepConnection[] $connections
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\Step[] $steps
 * @property-read \Illuminate\Database\Eloquent\Collection|\App\RuntimeStorage[] $storages
 * @mixin \Eloquent
 */
class Runtime extends Model
{
    protected $guarded = [];

    protected $casts = [
        'payload' => 'array',
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
            $nodes->push(new KahnNode($storage));
        }

        foreach($steps as $step) {
            $stepMap[$step->id] = $nodes->count();
            $nodes->push(new KahnNode($step));
        }

        // build the Adjacency lists and refs count
        foreach($connections as $conn) {
            $stepNode = $nodes[$stepMap[$conn->step_id]];
            $storageNode = $nodes[$storageMap[$conn->runtime_storage_id]];

            if ($conn->type == 'output') {
                $stepNode->adjList->push($storageNode);
                $storageNode->refCount++;
            } else {
                $storageNode->adjList->push($stepNode);
                $stepNode->refCount++;
            }
        }

        // Topological Ordering - Kahn's Algorithm
        $candidates = $nodes->filter(function($n) {
            return $n->refCount == 0;
        });

        $result = collect();
        foreach($nodes as $n) {
            if ($candidates->isEmpty()) break;

            $c = $candidates->pop();

            if ($c->v instanceof Step) {
                $result->push($c->v);
            }

            foreach($c->adjList as $a) {
                $a->refCount--;
                if ($a->refCount == 0) {
                    $candidates->push($a);
                }
            }
        }

        return $result;
    }

    /**
     * @return Step
     * @throws \Exception
     */
    public function runOneStep()
    {
        $steps = $this->getStepSequence();

        foreach($steps as $s) {
            if ($s->state == 'init' || $s->state == 'error') {
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

        return null;
    }

    public function createRuntimeDatabase()
    {
        DB::statement('CREATE DATABASE IF NOT EXISTS cceg_runtime_' . $this->id);
    }

    public function dropRuntimeDatabase()
    {
        DB::statement('DROP DATABASE IF EXISTS cceg_runtime_' . $this->id);
    }
}