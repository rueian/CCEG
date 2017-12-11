<?php

namespace App\StorageBuilder;


interface Builder
{
    static function getName();
    static function build($runtime, $key, $name, $payload);
    static function getFormSchema();
}