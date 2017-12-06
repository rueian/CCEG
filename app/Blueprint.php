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

            $blueprintStorages = $this->payload['storages'];
            foreach($blueprintStorages as $s) {
                switch ($s['type']) {
                    case 'table':
                        $storage = RuntimeStorage::createTableStorage($r, $s['key'], $s['schema']);
                        break;
                    case 'smt_result':
                        $storage = RuntimeStorage::createSMTResultTableStorage($r, $s['key']);
                        break;
                    case 'smt_input':
                        $storage = RuntimeStorage::createSMTInputStorage($r, $s['key'], $s['content']);
                        break;
                    case 'smt_output':
                        $storage = RuntimeStorage::createSMTOutputStorage($r, $s['key'], $s['content']);
                        break;
                    default:
                        throw new \Exception('Unsupported storage type: '.$s['type']);
                }
                $storageMap[$s['key']] = $storage;
            }

            $blueprintSteps = $this->payload['steps'];
            foreach($blueprintSteps as $s) {
                $input = $storageMap[$s['input']];
                $output = $storageMap[$s['output']];

                if (!$input) {
                    throw new \Exception('Undefined storage key: '.$s['input']);
                }
                if (!$output) {
                    throw new \Exception('Undefined storage key: '.$s['output']);
                }

                switch ($s['type']) {
                    case 'sql':
                        Step::createSQLStep($r, $s['name'], $s['note'], $input, $output, $s['param']);
                        break;
                    case 'smt':
                        Step::createSMTStep($r, $s['name'], $s['note'], $input, $output, $s['param']);
                        break;
                    case 'smt_output_to_table':
                        Step::createSMTOutputToTableStep($r, $s['name'], $s['note'], $input, $output, $s['param']);
                        break;
                    default:
                        throw new \Exception('Unsupported step type: '.$s['type']);
                }
            }
        } catch (\Exception $e) {
            DB::rollback();
            throw $e;
        }

        return $r;
    }
}
 