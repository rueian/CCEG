<?php

namespace App\Http\Controllers;

use Illuminate\Http\Request;
use Illuminate\Support\Facades\DB;

use App\Blueprint;
use App\Runtime;
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
        if (!preg_match('/^[\w]*$/', $request->input('name'))) {
            return response('儲存空間名稱僅可以是英數字與底線組合', 422);
        }
        if ($this->checkReservedWord($request->input('name'))) {
            return response('儲存空間名稱 ' . $request->input('name') . ' 是保留字，請更換', 422);
        }

        // check duplication field name
        $schema = $request->input('schema');
        $fields = array_pluck($schema, 'name');
        if (count($fields) != count(array_unique($fields))) {
            return response('請移除重複的欄位名稱', 422);
        }
        foreach ($fields as $field) {
            if (!preg_match('/^[\w]*$/', $field)) {
                return response('欄位名稱僅可以是英數字與底線組合', 422);
            }
        }
        foreach ($fields as $field) {
            if ($this->checkReservedWord($field)) {
                return response('欄位名稱 ' . $field . ' 是保留字，請更換', 422);
            }
        }

        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['storages'])) {
            $payload['storages'] = [];
        }

        $storageKey = $request->input('name');

        if (isset($payload['storages'][$storageKey])) {
            return response('儲存空間名稱 "' . $storageKey . '" 已經用過了', 422);
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

        if (!isset($payload['stepSeq'])) {
            $payload['stepSeq'] = 0;
        }
        $payload['stepSeq']++;
        $stepKey = 'step_' . strval($payload['stepSeq']);
        $stepOutputKey = $stepKey . '_result';

        if (isset($payload['steps'][$stepKey])) {
            return response('步驟代號 "' . $stepKey . '" 已經用過了', 422);
        }

        $stepPayload = $request->all();
        $stepPayload['output'] = $stepOutputKey;

        $stepRunner = Step::$runnerMap[$stepPayload['type']];
        $outputPayload = $stepRunner::getBlueprintStepStorage($payload['storages'], $stepPayload);
        $outputPayload['generated'] = true;
        $outputPayload['name'] = $stepOutputKey;
        if ($this->checkReservedWord($outputPayload['name'])) {
            return response('儲存空間名稱 ' . $outputPayload['name'] . ' 是保留字，請更換', 422);
        }

        // check duplication field name
        $fields = array_pluck($outputPayload['schema'], 'name');
        if (count($fields) != count(array_unique($fields))) {
            return response('請移除重複的輸出欄位名稱', 422);
        }
        foreach ($fields as $field) {
            if (!preg_match('/^[\w]*$/', $field)) {
                return response('輸出欄位名稱僅可以是英數字與底線組合', 422);
            }
        }
        foreach ($fields as $field) {
            if ($this->checkReservedWord($field)) {
                return response('欄位名稱 ' . $field . ' 是保留字，請更換', 422);
            }
        }

        $payload['storages'][$stepOutputKey] = $outputPayload;
        $payload['steps'][$stepKey] = $stepPayload;

        $blueprint->payload = $payload;
        $blueprint->save();

        return response()->json($blueprint);
    }

    public function editStep($id, $key, Request $request) {
        // return response()->json($request->input('content'));
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['steps'][$key])) {
            return response('該步驟不存在', 404);
        }

        if ($request->has('name')) {
            $payload['steps'][$key]['name'] = $request->input('name');
        }
        if ($request->has('note')) {
            $payload['steps'][$key]['note'] = $request->input('note');
        }
        if ($request->has('param')) {
            $payload['steps'][$key]['param'] = $request->input('param');
        }

        // regenerate output schema
        $stepOutputKey = $payload['steps'][$key]['output'];
        $stepRunner = Step::$runnerMap[$payload['steps'][$key]['type']];
        $outputPayload = $stepRunner::getBlueprintStepStorage($payload['storages'], $payload['steps'][$key]);
        $outputPayload['generated'] = true;
        $outputPayload['name'] = $stepOutputKey;
        // check duplication field name
        $fields = array_pluck($outputPayload['schema'], 'name');
        if (count($fields) != count(array_unique($fields))) {
            return response('請移除重複的輸出欄位名稱', 422);
        }
        foreach ($fields as $field) {
            if (!preg_match('/^[\w]*$/', $field)) {
                return response('輸出欄位名稱僅可以是英數字與底線組合', 422);
            }
        }
        // check missing field after update
        $oldSchema = $payload['storages'][$stepOutputKey]['schema'];
        foreach($oldSchema as $column) {
            $found = false;
            foreach($outputPayload['schema'] as $c) {
                if ($column['name'] == $c['name'] && $column['type'] == $c['type']) {
                    $found = true;
                }
            }
            if (!$found) {
                return response('更新失敗，因為在新的輸出儲存空間中找不到原有的欄位 ' . $column['name'] . '(' . $column['type'] . ')', 422);
            }
        }


        $payload['storages'][$stepOutputKey]['schema'] = $outputPayload['schema'];

        $blueprint->payload = $payload;
        $blueprint->save();

        return response()->json($blueprint);
    }

    public function removeStorage($id, $key)
    {
        $blueprint = Blueprint::findOrFail($id);
        $payload = $blueprint->payload;

        if (!isset($payload['storages'][$key])) {
            return response('該儲存空間不存在', 404);
        }

        if (isset($payload['storages'][$key]['generated'])) {
            return response('該儲存空間為上層步驟的輸出結果，若想刪除請直接刪除上層步驟', 422);
        }

        if (isset($payload['steps'])) {
            foreach ($payload['steps'] as $step) {
                foreach ($step['inputs'] as $inputKey => $inputStorageKey) {
                    if ($inputStorageKey == $key) {
                        return response('該儲存空間為下層步驟的輸入儲存空間，若想刪除請先刪除所有相關的下層步驟', 422);
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

    public function deleteRuntime($id, Request $request)
    {
        $r = Runtime::where('blueprint_id', $id)->where('id', $request->input('runtime_id'))->firstOrFail();

        $r->dropRuntimeDatabase();

        $r->delete();

        return response()->json([
            'redirect' => url('/blueprints/' . $r->blueprint_id . '/runtimes'),
            'runtime' => $r
        ]);
    }

    public function delete($id)
    {
        $blueprint = Blueprint::findOrFail($id);

        $runtimes = $blueprint->runtimes;

        DB::beginTransaction();
        try {
            foreach ($runtimes as $r) {
                $r->dropRuntimeDatabase();
                $r->delete();
            }
            $blueprint->delete();

            DB::commit();
        } catch (\Exception $e) {
            DB::rollback();

            return response()->json([
                'result' => 'error',
                'message' => $e->getMessage()
            ]);
        }

        return response()->json([
            'result' => 'success',
            'refresh' => true
        ]);
    }

    private function checkReservedWord($word)
    {
        $upper = strtoupper(trim($word));
        return in_array($upper, self::RESERVED_WORD);
    }

    // https://dev.mysql.com/doc/refman/8.0/en/keywords.html
    const RESERVED_WORD = [
        'ACCESSIBLE',
        'ADD',
        'ADMIN',
        'ALL',
        'ALTER',
        'ANALYZE',
        'AND',
        'AS',
        'ASC',
        'ASENSITIVE',
        'BEFORE',
        'BETWEEN',
        'BIGINT',
        'BINARY',
        'BLOB',
        'BOTH',
        'BY',
        'CALL',
        'CASCADE',
        'CASE',
        'CHANGE',
        'CHAR',
        'CHARACTER',
        'CHECK',
        'COLLATE',
        'COLUMN',
        'CONDITION',
        'CONSTRAINT',
        'CONTINUE',
        'CONVERT',
        'CREATE',
        'CROSS',
        'CUBE',
        'CUME_DIST',
        'CURRENT_DATE',
        'CURRENT_TIME',
        'CURRENT_TIMESTAMP',
        'CURRENT_USER',
        'CURSOR',
        'DATABASE',
        'DATABASES',
        'DAY_HOUR',
        'DAY_MICROSECOND',
        'DAY_MINUTE',
        'DAY_SECOND',
        'DEC',
        'DECIMAL',
        'DECLARE',
        'DEFAULT',
        'DELAYED',
        'DELETE',
        'DENSE_RANK',
        'DESC',
        'DESCRIBE',
        'DETERMINISTIC',
        'DISTINCT',
        'DISTINCTROW',
        'DIV',
        'DOUBLE',
        'DROP',
        'DUAL',
        'EACH',
        'ELSE',
        'ELSEIF',
        'EMPTY',
        'ENCLOSED',
        'ESCAPED',
        'EXCEPT',
        'EXISTS',
        'EXIT',
        'EXPLAIN',
        'FALSE',
        'FETCH',
        'FIRST_VALUE',
        'FLOAT',
        'FLOAT4',
        'FLOAT8',
        'FOR',
        'FORCE',
        'FOREIGN',
        'FROM',
        'FULLTEXT',
        'FUNCTION',
        'GENERATED',
        'GET',
        'GRANT',
        'GROUP',
        'GROUPING',
        'GROUPS',
        'HAVING',
        'HIGH_PRIORITY',
        'HOUR_MICROSECOND',
        'HOUR_MINUTE',
        'HOUR_SECOND',
        'IF',
        'IGNORE',
        'IN',
        'INDEX',
        'INFILE',
        'INNER',
        'INOUT',
        'INSENSITIVE',
        'INSERT',
        'INT',
        'INT1',
        'INT2',
        'INT3',
        'INT4',
        'INT8',
        'INTEGER',
        'INTERVAL',
        'INTO',
        'IO_AFTER_GTIDS',
        'IO_BEFORE_GTIDS',
        'IS',
        'ITERATE',
        'JOIN',
        'JSON_TABLE',
        'KEY',
        'KEYS',
        'KILL',
        'LAG',
        'LAST_VALUE',
        'LEAD',
        'LEADING',
        'LEAVE',
        'LEFT',
        'LIKE',
        'LIMIT',
        'LINEAR',
        'LINES',
        'LOAD',
        'LOCALTIME',
        'LOCALTIMESTAMP',
        'LOCK',
        'LONG',
        'LONGBLOB',
        'LONGTEXT',
        'LOOP',
        'LOW_PRIORITY',
        'MASTER_BIND',
        'MASTER_SSL_VERIFY_SERVER_CERT',
        'MATCH',
        'MAXVALUE',
        'MEDIUMBLOB',
        'MEDIUMINT',
        'MEDIUMTEXT',
        'MIDDLEINT',
        'MINUTE_MICROSECOND',
        'MINUTE_SECOND',
        'MOD',
        'MODIFIES',
        'NATURAL',
        'NOT',
        'NO_WRITE_TO_BINLOG',
        'NTH_VALUE',
        'NTILE',
        'NULL',
        'NUMERIC',
        'OF',
        'ON',
        'OPTIMIZE',
        'OPTIMIZER_COSTS',
        'OPTION',
        'OPTIONALLY',
        'OR',
        'ORDER',
        'OUT',
        'OUTER',
        'OUTFILE',
        'OVER',
        'PARTITION',
        'PERCENT_RANK',
        'PERSIST',
        'PERSIST_ONLY',
        'PRECISION',
        'PRIMARY',
        'PROCEDURE',
        'PURGE',
        'RANGE',
        'RANK',
        'READ',
        'READS',
        'READ_WRITE',
        'REAL',
        'RECURSIVE',
        'REFERENCES',
        'REGEXP',
        'RELEASE',
        'RENAME',
        'REPEAT',
        'REPLACE',
        'REQUIRE',
        'RESIGNAL',
        'RESTRICT',
        'RETURN',
        'REVOKE',
        'RIGHT',
        'RLIKE',
        'ROW',
        'ROWS',
        'ROW_NUMBER',
        'SCHEMA',
        'SCHEMAS',
        'SECOND_MICROSECOND',
        'SELECT',
        'SENSITIVE',
        'SEPARATOR',
        'SET',
        'SHOW',
        'SIGNAL',
        'SMALLINT',
        'SPATIAL',
        'SPECIFIC',
        'SQL',
        'SQLEXCEPTION',
        'SQLSTATE',
        'SQLWARNING',
        'SQL_BIG_RESULT',
        'SQL_CALC_FOUND_ROWS',
        'SQL_SMALL_RESULT',
        'SSL',
        'STARTING',
        'STORED',
        'STRAIGHT_JOIN',
        'SYSTEM',
        'TABLE',
        'TERMINATED',
        'THEN',
        'TINYBLOB',
        'TINYINT',
        'TINYTEXT',
        'TO',
        'TRAILING',
        'TRIGGER',
        'TRUE',
        'UNDO',
        'UNION',
        'UNIQUE',
        'UNLOCK',
        'UNSIGNED',
        'UPDATE',
        'USAGE',
        'USE',
        'USING',
        'UTC_DATE',
        'UTC_TIME',
        'UTC_TIMESTAMP',
        'VALUES',
        'VARBINARY',
        'VARCHAR',
        'VARCHARACTER',
        'VARYING',
        'VIRTUAL',
        'WHEN',
        'WHERE',
        'WHILE',
        'WINDOW',
        'WITH',
        'WRITE',
        'XOR',
        'YEAR_MONTH',
        'ZEROFILL',
    ];
}