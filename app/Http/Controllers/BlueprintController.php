<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;

use App\Blueprint;

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

    public function update($id, Request $request)
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
}