#lang racket/base

(provide google-sheets-csv-url
         google-sheets-csv
         google-sheets-table)

(require net/url)
(require 2htdp/batch-io)

(require "main.rkt")

(define sheet-csv-base-url
  (string->url "https://docs.google.com/spreadsheets/d/<ID>/export?format=csv"))

(define (google-sheets-csv-url id sheet)
  (url "https"
       #f
       "docs.google.com"
       #f
       #t
       (list
        (path/param "spreadsheets" '())
        (path/param "d" '())
        (path/param id '())
        (path/param "export" '()))
       `((format . "csv")
         ,@(if sheet
               `((gid . ,(format "~a" sheet)))
               `()))
       #f))

(define (google-sheets-csv id #:sheet [sheet #f])
  (define p (get-pure-port (google-sheets-csv-url id sheet) #:redirections 10))
  (define csv (parameterize ((current-input-port p)) (read-csv-file 'stdin)))
  (close-input-port p)
  csv)

(define (auto-convert-csv rows)
  (for/list [(row rows)]
    (for/list [(cell row)]
      (cond [(string->number cell)]
            [else cell]))))

(define (google-sheets-table id
                             #:sheet [sheet #f]
                             #:headings [headings #f]
                             #:auto-convert? [auto-convert? #t])
  (define csv ((if auto-convert? auto-convert-csv values) (google-sheets-csv id #:sheet sheet)))
  (csv-expr->table #:headings headings (if (and (pair? csv) headings) (cdr csv) csv)))

(module+ main
  ;; The demo from Pyret, https://twitter.com/PyretLang/status/773605473824145408
  (define planets
    (google-sheets-table "1-Avuufrt6TnI1Ba7v47NoOM7y_UGEEOH8kfcOBof9tU"
                         #:headings '(name mass gravity)))
  planets
  (define my-weight 80) ;; kilograms
  (table-extend planets [gravity] [weight-on (* my-weight (/ gravity 9.81))]))
