<?php

use Illuminate\Database\Seeder;
use App\Blueprint;

class ExampleBlueprintSeeder extends Seeder
{
    /**
     * Run the database seeds.
     *
     * @return void
     */
    public function run()
    {
        $b1 = new Blueprint;
        $b1->name = '按照排名分配成績';
        $b1->note = '輸入排名表與級距表，即可自動依排名分配成績';
        $b1->payload = json_decode('{"steps": {"step_1": {"name": "計算總人數", "type": "sql_select_map", "param": {"select": [{"as": "total", "expr": "COUNT(*)", "name": null, "type": "integer"}]}, "inputs": {"input": "student_ranks"}, "output": "step_1_result"}, "step_2": {"name": "帶入總人數", "note": "將總人數合併至 grade_interval 表，以便後續計算", "type": "sql_join", "param": {"method": "INNER JOIN"}, "inputs": {"left": "grade_interval", "right": "step_1_result"}, "output": "step_2_result"}, "step_3": {"name": "轉換百分比", "type": "sql_select_map", "param": {"select": [{"as": "grade_start", "expr": "grade_start", "type": "integer"}, {"as": "grade_end", "expr": "grade_end", "type": "integer"}, {"as": "percentage_start", "expr": "percentage_start", "type": "integer"}, {"as": "percentage_end", "expr": "percentage_end", "type": "integer"}, {"as": "total", "expr": "total", "type": "integer"}, {"as": "start", "expr": "percentage_start * total / 100", "name": null, "type": "integer"}, {"as": "end", "expr": "percentage_end * total / 100", "name": null, "type": "integer"}]}, "inputs": {"input": "step_2_result"}, "output": "step_3_result"}, "step_4": {"name": "合併學生排名", "type": "sql_join", "param": {"method": "LEFT JOIN", "conditions": [{"left": "rank", "right": "start", "operator": ">"}, {"left": "rank", "right": "end", "operator": "<="}]}, "inputs": {"left": "student_ranks", "right": "step_3_result"}, "output": "step_4_result"}, "step_5": {"name": "配分", "type": "sql_select_map", "param": {"select": [{"as": "rank", "expr": "rank", "type": "integer"}, {"as": "student_number", "expr": "student_number", "type": "varchar(255)"}, {"as": "grade", "expr": "grade_start - (((grade_start - grade_end) / (end - start)) * (rank - start - 1))", "name": null, "type": "float"}]}, "inputs": {"input": "step_4_result"}, "output": "step_5_result"}}, "stepSeq": 5, "storages": {"step_1_result": {"name": "step_1_result", "type": "table", "schema": [{"name": "total", "type": "integer"}], "generated": true}, "step_2_result": {"name": "step_2_result", "type": "table", "schema": [{"name": "grade_start", "type": "integer"}, {"name": "grade_end", "type": "integer"}, {"name": "percentage_start", "type": "integer"}, {"name": "percentage_end", "type": "integer"}, {"name": "total", "type": "integer"}], "generated": true}, "step_3_result": {"name": "step_3_result", "type": "table", "schema": [{"name": "grade_start", "type": "integer"}, {"name": "grade_end", "type": "integer"}, {"name": "percentage_start", "type": "integer"}, {"name": "percentage_end", "type": "integer"}, {"name": "total", "type": "integer"}, {"name": "start", "type": "integer"}, {"name": "end", "type": "integer"}], "generated": true}, "step_4_result": {"name": "step_4_result", "type": "table", "schema": [{"name": "rank", "type": "integer"}, {"name": "student_number", "type": "varchar(255)"}, {"name": "grade_start", "type": "integer"}, {"name": "grade_end", "type": "integer"}, {"name": "percentage_start", "type": "integer"}, {"name": "percentage_end", "type": "integer"}, {"name": "total", "type": "integer"}, {"name": "start", "type": "integer"}, {"name": "end", "type": "integer"}], "generated": true}, "step_5_result": {"name": "step_5_result", "type": "table", "schema": [{"name": "rank", "type": "integer"}, {"name": "student_number", "type": "varchar(255)"}, {"name": "grade", "type": "float"}], "generated": true}, "student_ranks": {"name": "student_ranks", "type": "table", "schema": [{"name": "rank", "type": "integer"}, {"name": "student_number", "type": "varchar(255)"}]}, "grade_interval": {"name": "grade_interval", "type": "table", "schema": [{"name": "grade_start", "type": "integer"}, {"name": "grade_end", "type": "integer"}, {"name": "percentage_start", "type": "integer"}, {"name": "percentage_end", "type": "integer"}]}}}', true);
        $b1->save();

        $b2 = new Blueprint;
        $b2->name = 'SMT 排課';
        $b2->note = '總共排四堂課的範例';
        $b2->payload = json_decode('{"steps": {"step_1": {"name": "排課", "type": "smt", "param": {"content": "macro_declare_int_var_set (x1 x2 y1 y2)\nmacro_var_set_mutually_exclusive (x1 x2 y1 y2)\nmacro_var_set_in_ranges (x1 x2 y1 y2) [10 20] [25 30]\nmacro_var_set_not_equal_cross (x1 x2 y1 y2) [8 16 24]\n(assert (= x2 (+ x1 1)))\n(assert (= y2 (+ y1 1)))"}, "inputs": {"input": "smt_replacements"}, "output": "step_1_result"}}, "stepSeq": 1, "storages": {"step_1_result": {"name": "step_1_result", "type": "table", "schema": [{"name": "variable", "type": "varchar(255)"}, {"name": "value", "type": "varchar(255)"}], "generated": true}, "smt_replacements": {"name": "smt_replacements", "type": "smt_variable_table", "schema": [{"name": "variable", "type": "varchar(255)"}, {"name": "value", "type": "varchar(255)"}]}}}', true);
        $b2->save();
    }
}
