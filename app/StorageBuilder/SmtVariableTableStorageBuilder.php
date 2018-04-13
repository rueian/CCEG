<?php
/**
 * Created by PhpStorm.
 * User: ruian
 * Date: 2017/12/29
 * Time: 上午1:03
 */

namespace App\StorageBuilder;


class SmtVariableTableStorageBuilder implements Builder
{
    static function getName()
    {
        return "SMT 變數表格";
    }

    static function build($runtime, $key, $name, $payload)
    {
        return TableStorageBuilder::build($runtime, $key, $name, [
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

    static function getFormSchema()
    {
        return [
            'type' => 'object',
            'required' => [
                'name',
            ],
            'properties' => [
                'name' => [
                    'type' => 'string',
                    'title' => '儲存空間名稱'
                ],
                'schema' => [
                    'type' => 'array',
                    'title' => '選擇欄位',
                    'items' => [
                        [
                            'type' => 'object',
                            'properties' => [
                                'name' => [
                                    'type' => 'string',
                                    'title' => '欄位名稱',
                                    'default' => 'variable',
                                ],
                                'type' => [
                                    'type' => 'string',
                                    'title' => '欄位型別',
                                    'default' => 'varchar(255)',
                                    'enum' => [
                                        'varchar(255)',
                                    ],
                                    'enumNames' => [
                                        '字串 (varchar(255))',
                                    ]
                                ],
                            ]
                        ],
                        [
                            'type' => 'object',
                            'properties' => [
                                'name' => [
                                    'type' => 'string',
                                    'title' => '欄位名稱',
                                    'default' => 'value',
                                ],
                                'type' => [
                                    'type' => 'string',
                                    'title' => '欄位型別',
                                    'default' => 'varchar(255)',
                                    'enum' => [
                                        'varchar(255)',
                                    ],
                                    'enumNames' => [
                                        '字串 (varchar(255))',
                                    ]
                                ],
                            ]
                        ]
                    ],
                ],
            ]
        ];
    }

    static function getFormUISchema()
    {
        return [
            'schema' => [
                'ui:readonly' => true
            ]
        ];
    }
}