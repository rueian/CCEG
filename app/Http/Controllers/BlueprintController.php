<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;

use App\Blueprint;
use App\Step;

class BlueprintController extends Controller
{
    public function index()
    {
        $blueprints = Blueprint::orderBy('id', 'desc')->get();

        return view('blueprints.index', compact('blueprints'));
    }

    public function store()
    {
        $blueprint = new Blueprint;
        $blueprint->name = '未命名';
        $blueprint->saveOrFail();

        return response()->json([
            'redirect' => url('/blueprints/'.$blueprint->id.'/edit'),
            'blueprint' => $blueprint
        ]);
    }

    public function edit($id)
    {
        $blueprint = Blueprint::findOrFail($id);

        return view('blueprints.edit', compact('blueprint'));
    }

    public function editable(Request $request)
    {
        $blueprint = Blueprint::findOrFail($request->input('pk'));

        if ($request->input('name') == 'name') {
            $blueprint->name = $request->input('value');
        } else if ($request->input('name') == 'note') {
            $blueprint->note = $request->input('value');
        } else {
            return response('field is not allowed', 422);
        }

        $blueprint->saveOrFail();

        return response('ok');
    }

    public function addStorage($id, Request $request)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['storages'])) {
            $payload['storages'] = [];
        }

        $storageKey = str_random(8);

        if (isset($payload['storages'][$storageKey])) {
            return response('資料源代號 "' . $storageKey . '" 已經用過了', 422);
        }

        $payload['storages'][$storageKey] = $request->all();
        $blueprint->payload = $payload;

        $blueprint->save();

        return response()->json($blueprint);
    }

    public function addStep($id, Request $request)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['steps'])) {
            $payload['steps'] = [];
        }

        $stepKey = str_random(8);
        $stepOutputKey = $stepKey . '_result';

        if (isset($payload['steps'][$stepKey])) {
            return response('步驟代號 "' . $stepKey . '" 已經用過了', 422);
        }

        $stepPayload = $request->all();
        $stepPayload['output'] = $stepOutputKey;

        $stepRunner = Step::$runnerMap[$stepPayload['type']];
        $outputPayload = $stepRunner::getBlueprintStepStorage($payload['storages'], $stepPayload);
        $outputPayload['generated'] = true;
        $outputPayload['name'] = $stepPayload['name'] . '的結果';

        $payload['storages'][$stepOutputKey] = $outputPayload;
        $payload['steps'][$stepKey] = $stepPayload;

        $blueprint->payload = $payload;
        $blueprint->save();

        return response()->json($blueprint);
    }

    public function removeStorage($id, $key)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['storages'][$key])) {
            return response('該資料源不存在', 404);
        }

        if (isset($payload['storages'][$key]['generated'])) {
            return response('該資料源為上層步驟的輸出結果，若想刪除請直接刪除上層步驟', 422);
        }

        if (isset($payload['steps'])) {
            foreach ($payload['steps'] as $step) {
                foreach ($step['inputs'] as $inputKey => $inputStorageKey) {
                    if ($inputStorageKey == $key) {
                        return response('該資料源為下層步驟的輸入資料源，若想刪除請先刪除所有相關的下層步驟', 422);
                    }
                }
            }
        }

        unset($payload['storages'][$key]);

        $blueprint->payload = $payload;
        $blueprint->save();

        return response()->json($blueprint);
    }

    public function removeStep($id, $key)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['steps'][$key])) {
            return response('該步驟不存在', 404);
        }

        $outputSotrageKey = $payload['steps'][$key]['output'];

        foreach ($payload['steps'] as $step) {
            foreach ($step['inputs'] as $inputKey => $inputStorageKey) {
                if ($inputStorageKey == $outputSotrageKey) {
                    return response('該步驟的輸出結果為下層步驟的輸入，若想刪除請先刪除所有相關的下層步驟', 422);
                }
            }
        }

        unset($payload['steps'][$key]);
        unset($payload['storages'][$outputSotrageKey]);

        $blueprint->payload = $payload;
        $blueprint->save();

        return response()->json($blueprint);
    }

    public function createRuntime($id)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['steps'])) {
            return response('該藍圖沒有任何步驟，請至少新增一個步驟', 422);
        }

        $r = $blueprint->buildRuntime();

        return response()->json([
            'redirect' => url('/blueprints/' . $blueprint->id . '/runtimes'),
            'runtime' => $r
        ]);
    }

    public function listRuntime($id, Request $request)
    {
        $blueprint = Blueprint::findOrFail($id);

        $runtimes = $blueprint->runtimes()->orderBy('id', 'desc')->get();

        $runtime = null;
        if ($runtimes->count() > 0) {
            $runtime = $runtimes[0];
            if ($request->has('runtime_id')) {
                $runtime = $runtimes->first(function ($r) use (&$request) {
                    return $r->id == $request->input('runtime_id');
                });
            }
        }

        return view('blueprints.runtimes', compact('blueprint', 'runtimes', 'runtime'));
    }
}