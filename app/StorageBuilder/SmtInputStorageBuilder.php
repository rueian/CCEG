<?php
/**
 * Created by PhpStorm.
 * User: ruian
 * Date: 2017/12/11
 * Time: 下午9:12
 */

namespace App\StorageBuilder;

use App\RuntimeStorage;

class SmtInputStorageBuilder implements Builder
{
    static function getName()
    {
        return 'SMT 輸入資料';
    }

    static function getFormSchema()
    {
        return [
            'type' => 'object',
            'required' => [
                'name',
                'key',
                'content'
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '資料源名稱'
                ],
                'key' => [
                    'type' => 'string',
                    'title' => '資料源代號'
                ],
                'content' => [
                    'type' => 'string',
                    'title' => 'SMT 輸入'
                ],
            ]
        ];
    }

    static function build($runtime, $key, $name, $payload)
    {
        $storage = new RuntimeStorage;
        $storage->runtime_id = $runtime->id;
        $storage->key = $key;
        $storage->name = $name;
        $storage->type = 'smt_input';
        $storage->state = 'init';
        $storage->payload = [
            'content' => $payload['content']
        ];

        $storage->save();

        return $storage;
    }
}