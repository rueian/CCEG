<?php

namespace App;

use Illuminate\Database\Eloquent\Model;
use Illuminate\Support\Facades\DB;

use App\Step;
use App\RuntimeStorage;
use App\Runtime;

class Blueprint extends Model
{
    protected $guarded = [];

    protected $casts = [
        'payload' => 'array'
    ];

    public function runtimes()
    {
        return $this->hasMany('App\Runtime');
    }

    public function buildRuntime()
    {
        $r = new Runtime;

        DB::beginTransaction();
        try {
            $r->blueprint_id = $this->id;
            $r->state = 'init';
            $r->save();

            $r->createRuntimeDatabase();

            $blueprintStorages = $this->payload['storages'];
            foreach($blueprintStorages as $key => $s) {
                switch ($s['type']) {
                    case 'table':
                        $storage = RuntimeStorage::createTableStorage($r, $key, $s['schema']);
                        break;
                    case 'smt_result':
                        $storage = RuntimeStorage::createSMTResultTableStorage($r, $key);
                        break;
                    case 'smt_input':
                        $storage = RuntimeStorage::createSMTInputStorage($r, $key, $s['content']);
                        break;
                    case 'smt_output':
                        $storage = RuntimeStorage::createSMTOutputStorage($r, $key, $s['content']);
                        break;
                    default:
                        throw new \Exception('Unsupported storage type: '.$s['type']);
                }
                $storageMap[$key] = $storage;
            }

            $blueprintSteps = $this->payload['steps'];
            foreach($blueprintSteps as $key => $s) {
                $inputs = [];
                foreach($s['inputs'] as $type => $k) {
                    $inputs[$type] = $storageMap[$k];
                }

                $output = $storageMap[$s['output']];

                Step::createStep($r, $key, $s['type'], $s['name'], $s['note'], $s['param'], $inputs, $output);
            }
        } catch (\Exception $e) {
            DB::rollback();
            throw $e;
        }

        return $r;
    }
}
 