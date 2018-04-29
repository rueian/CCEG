FROM php:7.2-apache

RUN docker-php-ext-install pdo_mysql

ENV APACHE_DOCUMENT_ROOT /src/public
RUN sed -ri -e 's!/var/www/html!${APACHE_DOCUMENT_ROOT}!g' /etc/apache2/sites-available/*.conf
RUN sed -ri -e 's!/var/www/!${APACHE_DOCUMENT_ROOT}!g' /etc/apache2/apache2.conf /etc/apache2/conf-available/*.conf

RUN a2enmod rewrite

RUN mkdir /src

COPY . /src

RUN chown -R www-data:www-data /src/storage && chown -R www-data:www-data /src/bootstrap/cache 

WORKDIR /src