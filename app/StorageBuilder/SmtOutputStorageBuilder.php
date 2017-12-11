<?php
/**
 * Created by PhpStorm.
 * User: ruian
 * Date: 2017/12/11
 * Time: 下午9:14
 */

namespace App\StorageBuilder;

use App\RuntimeStorage;

class SmtOutputStorageBuilder implements Builder
{
    static function getName()
    {
        return 'SMT 輸出資料';
    }

    static function getFormSchema()
    {
        return [];
    }

    static function build($runtime, $key, $name, $payload)
    {
        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->name = $name;
        $storage->type = 'smt_output';
        $storage->state = 'init';
        $storage->payload = [
            'content' => $payload['content']
        ];

        $storage->save();

        return $storage;
    }
}