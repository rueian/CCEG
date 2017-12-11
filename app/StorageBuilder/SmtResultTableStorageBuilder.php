<?php
/**
 * Created by PhpStorm.
 * User: ruian
 * Date: 2017/12/11
 * Time: 下午9:15
 */

namespace App\StorageBuilder;


class SmtResultTableStorageBuilder implements Builder
{

    static function build($runtime, $key, $payload)
    {
        return TableStorageBuilder::build($runtime, $key, [
            'schema' => [
                [
                    'name' => 'variable',
                    'type' => 'varchar(255)'
                ],
                [
                    'name' => 'value',
                    'type' => 'varchar(255)'
                ]
            ]
        ]);
    }
}