#lang racket/base

;; TODO: *lots* more tests

(provide (except-out (struct-out table) table)
         (rename-out [make-table table] [table <table>])

         (struct-out table-column)
         (struct-out table-column-computed)
         (struct-out table-column-aggregate)
         (struct-out table-ordering)
         (struct-out table-header)

         empty-table

         table-column-names
         table-column-count
         table-row-count
         table-empty?
         table-row-ref
         table-column-ref

         table-rename*
         table-rename

         table-extend*
         table-extend

         table-freeze-aggregate

         table-select*
         table-select
         table-reject*
         table-reject

         table-filter*
         table-filter

         table-group-by**
         table-group-by*
         table-group-by

         table-value<?
         table-order*
         table-order

         table-iterator?
         in-table

         table-append

         table-cross-join
         table-equi-join
         table-natural-join

         ->table

         table->hashes

         ;; TODO: Nice syntax for sequences-of-structs -> table
         ;; struct->list*
         ;; structs->table

         strings->table/rx

         csv-expr->table
         table->csv-expr

         pretty-print-table
         table->pretty-string)

(require racket/dict)
(require racket/format)
(require racket/function)
(require racket/match)
(require racket/pretty)
(require racket/set)
(require racket/stream)
(require racket/vector)
(require data/order)

(module+ test (require rackunit) (provide (all-defined-out)))

;; A Table is a data structure having zero or more named columns.
;;
;; Columns are named by symbol.
;; Columns must not shadow each other. Use table-rename.

(struct table-column
  (name) ;; Symbol
  #:prefab)

(struct table-column-computed table-column
  (dependencies ;; Listof Symbol, length n
   proc)        ;; (Any ...n -> Any)
  #:prefab)

(struct table-column-aggregate table-column
  (dependencies   ;; Listof Symbol, length n
   seed-proc      ;; (Any ...n -> Any)
   combiner-proc) ;; (Any Any -> Any)
  #:prefab)

(define (table-column-dependencies c)
  (cond [(table-column-computed? c) (table-column-computed-dependencies c)]
        [(table-column-aggregate? c) (table-column-aggregate-dependencies c)]
        [(table-column? c) '()]))

(define (table-column-positional? c)
  (not (table-column-aggregate? c)))

(struct table-ordering
  (column          ;; Symbol
   less-than-proc) ;; Any Any -> Boolean
  #:prefab)

(struct table-header
  (columns ;; Listof Column
   index)  ;; Map Symbol Nat -- missing entry means aggregate.
  #:transparent
  #:methods gen:equal+hash
  [(define (equal-proc h1 h2 =?)
     (=? (characterize-table-columns h1)
         (characterize-table-columns h2)))
   (define (hash-proc h hash) (hash (characterize-table-columns h)))
   (define (hash2-proc h hash) (hash (characterize-table-columns h)))])

(struct table
  (header*    ;; TableHeader
   aggregates ;; Map Symbol Any
   body)      ;; TableBody
  #:transparent
  #:property prop:sequence
  (lambda (t) (in-table* t (table-column-names t)))
  #:methods gen:custom-write
  [(define (write-proc t port mode)
     (write-string (table->pretty-string t) port))]
  #:methods gen:equal+hash
  [(define (equal-proc t1 t2 =?)
     (and (=? (table-header* t1) (table-header* t2))
          (=? (table-aggregates t1) (table-aggregates t2))
          (=? (vector-length (table-body t1)) (vector-length (table-body t2)))
          (let* ((cs1 (filter table-column-positional? (table-columns t1)))
                 (dep-index (make-dep-index t2 (map table-column-name cs1))))
            (for/and [(r1 (in-vector (table-body t1)))
                      (r2 (in-vector (table-body t2)))]
              (equal? r1 (list->vector (deref-dep-index r2 dep-index)))))))
   (define (hash-proc t hash) (gen-table-hash t hash bitwise-xor))
   (define (hash2-proc t hash) (gen-table-hash t hash +))])

(define (gen-table-hash t hash ++)
  (++ (hash (table-header* t))
      (hash (table-aggregates t))
      (for*/fold [(v 0)] [(row (in-vector (table-body t))) (col (in-vector row))]
        (++ v (hash col)))))

;; A TableBody is a Vectorof TableRow.
;; A TableRow is a Vectorof Any, with as many elements as there are non-aggregate columns.

(define (table-columns t)
  (table-header-columns (table-header* t)))

(define (table-index t)
  (table-header-index (table-header* t)))

(define (table-column-names t)
  (for/set [(c (table-columns t))]
    (table-column-name c)))

(define (table-column-count t)
  (length (table-columns t)))

(define (table-row-count t)
  (vector-length (table-body t)))

(define (table-empty? t)
  (zero? (table-row-count t)))

(define (table-row-ref n t)
  (vector-ref (table-body t) n))

(define (table-column-ref col-name t)
  (define i (make-dep-index/aggregates 'table-column-ref t (list col-name)))
  (for/list [(row (in-vector (table-body t)))] (deref-dep-index-pos row (car i))))

(define (simple-table-header col-specs)
  (table-header col-specs
                (for/fold [(i (hasheq))]
                          [(c (in-list col-specs)) #:when (table-column-positional? c)]
                  (hash-set i (table-column-name c) (hash-count i)))))

(define-syntax-rule (make-table [col-name ...] [value ...] ...)
  (table (simple-table-header (list (table-column 'col-name) ...))
         (hasheq)
         (vector (vector value ...) ...)))

(define empty-table (make-table []))

(define (table-rename* t name-map)
  (struct-copy table t
    [header* (table-header (map (rename-column name-map) (table-columns t))
                           (for/hasheq [((old-name i) (in-hash (table-index t)))]
                             (values (name-map old-name) i)))]
    [aggregates (for/hasheq [((old-name v) (in-hash (table-aggregates t)))]
                  (values (name-map old-name) v))]))

(define ((rename-column name-map) c)
  (match c
    [(table-column-computed old-name deps proc)
     (table-column-computed (name-map old-name) (map name-map deps) proc)]
    [(table-column-aggregate old-name deps seed comb)
     (table-column-aggregate (name-map old-name) (map name-map deps) seed comb)]
    [(table-column old-name)
     (table-column (name-map old-name))]))

(define-syntax-rule (table-rename table [new-name old-name] ...)
  (let ((m (make-hasheq (list (cons 'old-name 'new-name) ...))))
    (table-rename* table (lambda (n) (hash-ref m n n)))))

;; Table (Listof Symbol) -> (Listof (Option Nat))
(define (make-dep-index t deps)
  (for/list [(dep (in-list deps))]
    (hash-ref (table-index t) dep #f)))

;; Symbol Table (Listof Symbol) -> (Listof (U Nat (List Any)))
(define (make-dep-index/aggregates who t deps)
  (if (table-empty? t)
      '()
      (for/list [(dep deps)]
        (hash-ref (table-index t)
                  dep
                  (lambda ()
                    ;; Wrap aggregate values in a marker list
                    (list (hash-ref (table-aggregates t)
                                    dep
                                    (lambda ()
                                      (error who "Column ~v does not exist" dep)))))))))

(define (deref-dep-index row is)
  (for/list [(i (in-list is))] (deref-dep-index-pos row i)))

(define (deref-dep-index-pos row i)
  (if (list? i) ;; wrapped aggregate value
      (car i)
      (vector-ref row i)))

(define (extend-table-header-index h positional-col-specs)
  (for/fold [(index (table-header-index h))] [(c positional-col-specs)]
    (hash-set index (table-column-name c) (hash-count index))))

(define (table-extend* t deps col-specs)
  ;; Enforce that deps lists are eq?.
  (for [(c col-specs)]
    (when (not (eq? deps (table-column-dependencies c)))
      (error 'table-extend*
             "Dependencies of new column ~v do not match the master list ~v"
             c
             deps)))
  ;; Enforce name uniqueness.
  (for/fold [(names (table-column-names t))] [(c col-specs)]
    (if (set-member? names (table-column-name c))
        (error 'table-extend*
               "New column ~v would shadow an existing or new column"
               c)
        (set-add names c)))
  ;; Enforce that new columns are either computed or aggregate
  (define bads (filter (lambda (c) (not (or (table-column-computed? c)
                                            (table-column-aggregate? c))))
                       col-specs))
  (when (not (null? bads))
    (error 'table-extend*
           "Unexpected new table column types ~v"
           bads))
  ;; Compute dependency index.
  ;; Separate out new aggregates.
  (define aggs (filter table-column-aggregate? col-specs))
  (define maps (filter table-column-computed? col-specs))
  ;; Compute new aggregates and rows, if rows already exist.
  (define dep-index (make-dep-index/aggregates 'table-extend* t deps))
  (define-values (new-aggregates new-rows-rev)
    (for/fold [(aggregates (table-aggregates t)) (rows-rev '())]
              [(old-row (in-vector (table-body t)))]
      (define dep-vals (deref-dep-index old-row dep-index))
      (values (for/fold [(aggregates aggregates)] [(c aggs)]
                (define n (table-column-name c))
                (define v (apply (table-column-aggregate-seed-proc c) dep-vals))
                (define v1
                  (if (hash-has-key? aggregates n)
                      ((table-column-aggregate-combiner-proc c) (hash-ref aggregates n) v)
                      v))
                (hash-set aggregates n v1))
              (cons (vector-append old-row (for/vector [(c maps)]
                                             (apply (table-column-computed-proc c) dep-vals)))
                    rows-rev))))
  (table (table-header (append (table-columns t) col-specs)
                       (extend-table-header-index (table-header* t) maps))
         new-aggregates
         (list->vector (reverse new-rows-rev))))

(define-syntax-rule (table-extend table [col-name ...] col-spec ...)
  (let ((deps (list 'col-name ...)))
    (table-extend* table deps (list (parse-col-spec deps (col-name ...) col-spec) ...))))

(define-syntax parse-col-spec
  (syntax-rules ()
    [(_ deps args [col-name expr])
     (table-column-computed 'col-name deps (lambda args expr))]
    [(_ deps args [col-name combiner-fn-expr seed-expr])
     (table-column-aggregate 'col-name deps (lambda args seed-expr) combiner-fn-expr)]))

(define (table-freeze-aggregate col-name t)
  (define c (findf (lambda (c) (and (table-column-aggregate? c)
                                    (eq? (table-column-name c) col-name)))
                   (table-columns t)))
  (when (not c) (error 'table-freeze-aggregate "No such aggregate column ~v" col-name))
  (define vv (vector (hash-ref (table-aggregates t) col-name 'missing-means-no-table-rows-at-all)))
  (table (table-header (append (remq c (table-columns t)) (list (table-column col-name)))
                       (let ((i (table-index t)))
                         (hash-set i col-name (hash-count i))))
         (hash-remove (table-aggregates t) col-name)
         (for/vector [(row (in-vector (table-body t)))]
           (vector-append row vv))))

(define (table-select** who col-names t)
  (define new-col-specs (filter (lambda (c) (set-member? col-names (table-column-name c)))
                                (table-columns t)))
  (when (not (= (set-count col-names) (length new-col-specs)))
    (define missing (set-subtract col-names (list->set (map table-column-name new-col-specs))))
    (error who "Attempted to retain nonexistent columns ~v" missing))
  (define new-aggregates
    (if (table-empty? t)
        (hasheq)
        (for/hasheq [(c new-col-specs) #:when (table-column-aggregate? c)]
          (when (not (subset? (list->set (table-column-dependencies c)) col-names))
            (define missing (set-subtract (list->set (table-column-dependencies c))
                                          col-names))
            (error who
                   "Cannot retain column ~v because it depends on columns ~v"
                   c
                   missing))
          (values (table-column-name c) (hash-ref (table-aggregates t) (table-column-name c))))))
  (table (simple-table-header new-col-specs)
         new-aggregates
         (let* ((maps (filter table-column-positional? new-col-specs))
                (dep-index (make-dep-index t (map table-column-name maps))))
           (for/vector [(old-row (in-vector (table-body t)))]
             (for/vector [(i dep-index)] (vector-ref old-row i))))))

(define (table-select* col-names t)
  (table-select** 'table-select* col-names t))

(define-syntax-rule (table-select [col-name ...] table)
  (table-select* (set 'col-name ...) table))

(define (table-reject* col-names t)
  (table-select** 'table-reject* (set-subtract (table-column-names t) col-names) t))

(define-syntax-rule (table-reject [col-name ...] table)
  (table-reject* (set 'col-name ...) table))

(define (table-filter* t deps pred)
  (recompute-aggregates
   (struct-copy table t
     [body
      (let ((dep-index (make-dep-index/aggregates 'table-filter* t deps)))
        (for/vector [(old-row (in-vector (table-body t)))
                     #:when (apply pred (deref-dep-index old-row dep-index))]
          old-row))])))

(define-syntax-rule (table-filter table [col-name ...] expr ...)
  (table-filter* table (list 'col-name ...)
                 (lambda (col-name ...) (and expr ...))))

(define (table-group-by** t deps class-proc #:hash-type [base-hash hash])
  (define dep-index (make-dep-index/aggregates 'table-group-by** t deps))
  (define classes-rev
    (for/fold [(classes-rev (base-hash))] [(old-row (in-vector (table-body t)))]
      (define class (apply class-proc (deref-dep-index old-row dep-index)))
      (hash-set classes-rev class (cons old-row (hash-ref classes-rev class '())))))
  (for/list [((class rows-rev) (in-hash classes-rev))]
    (cons class
          (recompute-aggregates
           (struct-copy table t [body (list->vector (reverse rows-rev))])))))

(define (table-group-by* t deps class-proc #:hash-type [base-hash hash])
  (map cdr (table-group-by** t deps class-proc #:hash-type base-hash)))

(define-syntax table-group-by
  (syntax-rules ()
    [(_ table #:hash-type base-hash [col-name ...] expr)
     (table-group-by* table (list 'col-name ...) (lambda (col-name ...) expr)
                      #:hash-type base-hash)]
    [(_ table [col-name ...] expr)
     (table-group-by* table (list 'col-name ...) (lambda (col-name ...) expr))]))

(define (table-order* t orderings)
  (struct-copy table t
    [body
     (list->vector
      (foldr (lambda (o rows)
               (define i (car (make-dep-index t (list (table-ordering-column o)))))
               (when (not i)
                 (error 'table-order* "Cannot order by column ~v" (table-ordering-column o)))
               (sort rows (table-ordering-less-than-proc o) #:key (lambda (r) (vector-ref r i))))
             (vector->list (table-body t))
             orderings))]))

(define-syntax-rule (table-order table [order-spec ...] ...)
  (table-order* table (list (parse-table-ordering order-spec ...) ...)))

(define datum<? (order-<? datum-order))
(define (table-value<? a b)
  (if (and (number? a) (number? b))
      (< a b)
      (datum<? a b)))

(define ((flip f) a b) (f b a))

(define-syntax parse-table-ordering
  (syntax-rules (ascending descending)
    [(_ col-name ascending)    (table-ordering 'col-name table-value<?)]
    [(_ col-name ascending <)  (table-ordering 'col-name <)]
    [(_ col-name descending)   (table-ordering 'col-name (flip table-value<?))]
    [(_ col-name descending <) (table-ordering 'col-name (flip <))]))

(struct table-iterator (table dep-index index)
  #:transparent
  #:methods gen:stream
  [(define (stream-empty? i)
     (>= (table-iterator-index i)
         (table-row-count (table-iterator-table i))))
   (define (stream-first i)
     (apply values
            (deref-dep-index (vector-ref (table-body (table-iterator-table i))
                                         (table-iterator-index i))
                             (table-iterator-dep-index i))))
   (define (stream-rest i)
     (struct-copy table-iterator i [index (+ (table-iterator-index i) 1)]))])

(define (in-table* t col-names)
  (table-iterator t (make-dep-index/aggregates 'in-table* t col-names) 0))

(define-syntax in-table
  (syntax-rules ()
    [(_ table [col-name ...]) (in-table* table (list 'col-name ...))]
    [(_ table) (let ((t table)) (in-table* t (table-column-names t)))]))

(define (table-append . tables)
  (if (null? tables)
      empty-table
      (let ((expected-characterization (characterize-table-columns (table-header* (car tables))))
            (aggregate-col-specs (filter table-column-aggregate? (table-columns (car tables)))))
        (foldl (table-append* expected-characterization aggregate-col-specs)
               (car tables)
               (cdr tables)))))

(define (characterize-table-columns h)
  (make-immutable-hash (map (lambda (c) (cons (table-column-name c) (table-column-aggregate? c)))
                            (table-header-columns h))))

(define ((table-append* expected-characterization aggregate-col-specs) rhs lhs) ;; yes, flipped
  ;; We *should* check that column definitions are *identical* here,
  ;; except we don't have a good enough predicate to use for aggregate
  ;; functions. We could use `eq?` and rely on
  ;; syntax-local-lift-expression in `parse-col-spec`, but it seems
  ;; better just not to try too hard here.
  ;;
  ;; Also, TODO: repeated vector-append is O(n^2). Can do better.
  ;;
  (when (not (equal? expected-characterization (characterize-table-columns (table-header* rhs))))
    (error 'table-append "Mismatch between available columns"))
  (struct-copy table lhs
    [aggregates
     (merge-aggregates aggregate-col-specs (table-aggregates lhs) (table-aggregates rhs))]
    [body
     (vector-append (table-body lhs) (adjust-table-body (table-header* lhs) rhs))]))

(define (adjust-table-body target-header source-t)
  (define dep-index (make-dep-index source-t (filter table-column-positional?
                                                     (table-header-columns target-header))))
  (for/vector [(source-row (in-vector (table-body source-t)))]
    (deref-dep-index source-row dep-index)))

(define (recompute-aggregates t)
  (struct-copy table t
    [aggregates
     (if (table-empty? t)
         (hasheq)
         (for/hasheq [(c (table-columns t))
                      #:when (table-column-aggregate? c)]
           (define dep-index (make-dep-index/aggregates 'recompute-aggregates
                                                        t
                                                        (table-column-aggregate-dependencies c)))
           (define (seed row) (apply (table-column-aggregate-seed-proc c)
                                     (deref-dep-index row dep-index)))
           (define combiner (table-column-aggregate-combiner-proc c))
           (values (table-column-name c)
                   (for/fold [(v (seed (vector-ref (table-body t) 0)))]
                             [(row (in-vector (table-body t) 1))]
                     (combiner v (seed row))))))]))

(define *merge-sentinel* (cons '*merge-sentinel* '()))
(define (merge-aggregates col-specs a1 a2)
  (for/fold [(a (hasheq))] [(c (in-list col-specs))]
    (define n (table-column-name c))
    (define v1 (hash-ref a1 n *merge-sentinel*))
    (define v2 (hash-ref a2 n *merge-sentinel*))
    (cond
      [(eq? v1 *merge-sentinel*) (if (eq? v2 *merge-sentinel*) a (hash-set a n v2))]
      [(eq? v2 *merge-sentinel*) (hash-set a n v1)]
      [else (hash-set a n ((table-column-aggregate-combiner-proc c) v1 v2))])))

(define (ensure-no-column-name-collisions! who t1 t2 except2)
  (define colliding-column-names (set-intersect (table-column-names t1)
                                                (set-subtract (table-column-names t2)
                                                              (list->set except2))))
  (when (not (set-empty? colliding-column-names))
    (error who "Colliding column names: ~v" colliding-column-names)))

(define (table-cross-join* t1 t2)
  (ensure-no-column-name-collisions! 'table-cross-join* t1 t2 '())
  (define h1 (table-header* t1))
  (define h2 (table-header* t2))
  (recompute-aggregates
   (table (table-header (append (table-header-columns h1) (table-header-columns h2))
                        (extend-table-header-index h1 (filter table-column-positional?
                                                              (table-header-columns h2))))
          (for/fold [(a (table-aggregates t1))] [((k v) (in-hash (table-aggregates t2)))]
            (hash-set a k v))
          (for*/vector [(row1 (in-vector (table-body t1)))
                        (row2 (in-vector (table-body t2)))]
            (vector-append row1 row2)))))

(define (table-cross-join . tables)
  (if (null? tables)
      empty-table
      (foldl (lambda (rhs lhs) (table-cross-join* lhs rhs))
             (car tables)
             (cdr tables))))

;; NB. Groups of rows are in reverse order.
(define (index-rows-by t dep-index)
  (for/fold [(i (hash))] [(row (in-vector (table-body t)))]
    (define k (deref-dep-index row dep-index))
    (hash-set i k (cons row (hash-ref i k '())))))

(define (table-equi-join* t1 t2 column-name-alist #:discard-redundant? [discard-redundant? #t])
  (define ns1 (map car column-name-alist))
  (define ns2 (map cdr column-name-alist))
  (ensure-no-column-name-collisions! 'table-equi-join* t1 t2 (if discard-redundant? ns2 '()))
  (define h1 (table-header* t1))
  (define h2 (table-header* t2))
  (define dep-index1 (make-dep-index/aggregates 'table-equi-join* t1 ns1))
  (define dep-index2 (make-dep-index/aggregates 'table-equi-join* t2 ns2))
  (define keep-col-specs (if discard-redundant?
                             (filter (lambda (c) (not (memq (table-column-name c) ns2)))
                                     (table-header-columns h2))
                             (table-header-columns h2)))
  (define keep-dep-index
    (and discard-redundant?
         (make-dep-index t2
                         (map table-column-name (filter table-column-positional? keep-col-specs)))))
  (define i2 (index-rows-by t2 dep-index2))
  (recompute-aggregates
   (table (table-header (append (table-header-columns h1) keep-col-specs)
                        (extend-table-header-index h1 (filter table-column-positional?
                                                              keep-col-specs)))
          (hasheq) ;; will be recomputed immediately
          (for*/vector [(row1 (in-vector (table-body t1)))
                        (row2 (in-list
                               (reverse (hash-ref i2 (deref-dep-index row1 dep-index1) '()))))]
            (vector-append row1
                           (if discard-redundant?
                               (list->vector (deref-dep-index row2 keep-dep-index))
                               row2))))))

(define-syntax-rule (table-equi-join table1 table2 [col-name1 col-name2] ...)
  (table-equi-join* table1 table2 (list (cons 'col-name1 'col-name2) ...)))

(define (table-natural-join t1 t2)
  (define mapping (for/list [(n (in-set (set-intersect (table-column-names t1)
                                                       (table-column-names t2))))]
                    (cons n n)))
  (table-equi-join* t1 t2 mapping #:discard-redundant? #t))

;; sequence of rows
;; each row can be a sequence or a dict
;; column names must be supplied to work with sequence rows; may be omitted for dict rows
;; every value in a sequence row is turned into a column
;; if column names supplied, then only supplied names are extracted from dict rows
;; if column names not supplied, every name is extracted from dict rows
;; in all cases, every resulting row must have exactly the same columns available
(define (->table #:columns [col-names0 #f] raw-data)
  (define col-names (or col-names0 (find-column-names raw-data)))
  (define col-names-set (list->set col-names))
  (table (simple-table-header (map table-column col-names))
         (hasheq)
         (for/vector [(raw-row raw-data)]
           (cond
             [(dict? raw-row)
              (define ns (list->set (dict-keys raw-row)))
              (when (not (equal? col-names-set ns))
                (error '->table "Inconsistent column names: expected ~v, got ~v" col-names-set ns))
              (for/vector [(n col-names)] (dict-ref raw-row n))]
             [(sequence? raw-row)
              (when (not col-names0)
                (error '->table
                       "Explicit column names must be given to work with sequences as rows"))
              (for/vector [(v raw-row)] v)]
             [else
              (error '->table "Unsupported raw row: ~v" raw-row)]))))

(define (find-column-names raw-data)
  (define h
    (for/or [(raw-row raw-data)]
      (cond [(dict? raw-row) raw-row]
            [(sequence? raw-row)
             (error '->table
                    "Explicit column names must be given to work with sequences as rows")]
            [else #f])))
  (when (not h) (error '->table "Cannot infer column names"))
  (sort (dict-keys h) table-value<?))

(define (table->hashes t)
  (define col-specs (table-columns t))
  (define col-names (map table-column-name col-specs))
  (define dep-index (make-dep-index/aggregates 'table->hashes t col-names))
  (for/list [(row (in-vector (table-body t)))]
    (for/hash [(n (in-list col-names))
               (v (in-list (deref-dep-index row dep-index)))]
      (values n v))))

;; (define (struct->list* . accessors)
;;   (lambda (s)
;;     (for/list [(accessor (in-list accessors))] (accessor s))))

;; (structs->table struct:foo [field-name ...] (list (foo ...) (foo ...)))

(define (strings->table/rx r col-names strings #:strict? [strict? #t])
  (table (simple-table-header (map table-column (filter symbol? col-names)))
         (hasheq)
         (for*/vector [(s strings)
                       (m (in-value (regexp-match r s)))
                       #:when (or m (if strict?
                                        (error 'strings->table/rx "Regexp failed to match: ~v" s)
                                        #f))]
           (for/vector [(capture (in-list (cdr m)))
                        (name (in-list col-names))
                        #:when name]
             capture))))

(define (csv-expr->table #:headings [headings0 #f] rows0)
  (define guessing-headings? (not headings0))
  (define headings (or headings0
                       (if (null? rows0)
                           (error 'csv-expr->table "Cannot guess headings when no rows present")
                           (car rows0))))
  (define rows (if guessing-headings?
                   (cdr rows0)
                   rows0))
  (define col-names (map (lambda (x) (string->symbol (~a x))) headings))
  (define column-count (length col-names))
  (table (simple-table-header (map table-column col-names))
         (hasheq)
         (for/vector [(row rows)]
           (when (not (= (length row) column-count))
             (error 'csv-expr->table "Ragged row; expected ~v columns, got: ~v" column-count row))
           (list->vector row))))

(define (table->csv-expr t #:headings? [headings? #t])
  (define col-specs (table-columns t))
  (define col-names (map table-column-name col-specs))
  (define dep-index (make-dep-index/aggregates 'table->csv-expr t col-names))
  (define rows
    (for/list [(row (in-vector (table-body t)))]
      (deref-dep-index row dep-index)))
  (if headings?
      (cons col-names rows)
      rows))

(define (pretty-print-table t [p (current-output-port)])
  (define col-specs (table-columns t))
  (define separator "|")
  (define separator-width (string-length separator))
  (define minimum-actual-allocation 8)

  ;; Rescales the column widths to try to conform to the given width limit.
  (define (scale-widths requested-widths total-width-limit)
    (define numbered-reqs (for/list [(i (in-naturals)) (w requested-widths)] (list w i)))
    (define sorted-reqs (sort numbered-reqs #:key car <))
    (define-values (_total-request sorted-reqs+totals)
      (let loop ((reqs sorted-reqs))
        (match reqs
          ['() (values 0 '())]
          [(cons (list w i) reqs)
           (define-values (total tail) (loop reqs))
           (define next-total (+ total w separator-width))
           (values next-total (cons (list w i next-total) tail))])))
    (define scaled-reqs
      (let loop ((reqs sorted-reqs+totals) (remaining-space total-width-limit))
        (match reqs
          ['() '()]
          [(cons (list w i total) reqs)
           (if (>= remaining-space total)
               (cons (list w i)
                     (loop reqs (- remaining-space w separator-width)))
               (let ((allocation (if (< w minimum-actual-allocation)
                                     w
                                     (max minimum-actual-allocation
                                          (floor (* w (/ remaining-space total)))))))
                 (cons (list allocation i)
                       (loop reqs (- remaining-space allocation separator-width)))))])))
    (map car (sort scaled-reqs #:key cadr <)))

  (define (column-width c)
    (max (string-length (~a (table-column-name c)))
         (if (table-column-aggregate? c)
             (string-length (~v (hash-ref (table-aggregates t) (table-column-name c) "")))
             (let ((i (hash-ref (table-index t) (table-column-name c))))
               (for/fold [(acc 0)] [(row (in-vector (table-body t)))]
                 (max acc (string-length (~v (vector-ref row i)))))))))

  (define widths (scale-widths (map column-width col-specs) (pretty-print-columns)))

  (define (pad-or-truncate ->string v w k)
    (define s (->string v))
    (define len (string-length s))
    (define padding (- w len))
    (if (negative? padding)
        (string-append (substring s 0 (max 0 (- w 2))) "..")
        (k s padding)))

  (define (centeralign ->string v w)
    (pad-or-truncate
     ->string v w
     (lambda (s padding)
       (define left-padding (arithmetic-shift padding -1))
       (define right-padding (- padding left-padding))
       (string-append (make-string left-padding #\space) s (make-string right-padding #\space)))))

  (define (leftalign ->string v w)
    (pad-or-truncate
     ->string v w
     (lambda (s padding)
       (string-append s (make-string (max 0 padding) #\space)))))

  (define ((output align ->string) v w)
    (display (align ->string v w) p))

  (define (output-columns o vs)
    (for/fold [(need-sep? #f)] [(v vs) (w widths)]
      (when need-sep? (display separator p))
      (o v w)
      #t)
    (newline p))

  (output-columns (output centeralign ~a) (map table-column-name col-specs))
  (displayln (make-string (+ (* separator-width (- (length widths) 1))
                             (foldl + 0 widths))
                          #\-)
             p)

  (define dep-index (make-dep-index t (map table-column-name col-specs)))
  (for [(row (in-vector (table-body t)))]
    (output-columns (output leftalign ~v) (deref-dep-index row dep-index))))

(define (table->pretty-string t)
  (define p (open-output-string))
  (pretty-print-table t p)
  (get-output-string p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (require (only-in racket/string string-join))

  (define my-table
    (make-table [timestamp    name            age president]
                ["2016-01-01" "James McAvoy"  30  "Magneto"]
                ["2016-01-02" "Matt Murdock"  35  "Stick"]
                ["2016-01-03" "Shallan Davar" 20  "Stick"]))

  (check-equal? (table->pretty-string my-table)
                (string-join (list " timestamp  |     name      |age|president"
                                   "------------------------------------------"
                                   "\"2016-01-01\"|\"James McAvoy\" |30 |\"Magneto\""
                                   "\"2016-01-02\"|\"Matt Murdock\" |35 |\"Stick\"  "
                                   "\"2016-01-03\"|\"Shallan Davar\"|20 |\"Stick\"  "
                                   "")
                             "\n"))

  (define world
    (make-table [name gdp pop area]
                ["Atlantis" 1000 10 0]
                ["Amestris" 9999 1000 5000]
                ["Kamina City" 2000 9999 9999]))

  (let ((extended-world (table-extend world [gdp pop area]
                                      [gdp-per-pop (exact->inexact (/ gdp pop))]
                                      [total-area + area]))
        (check-world (make-table [name gdp pop area gdp-per-pop]
                                 ["Atlantis" 1000 10 0 100.0]
                                 ["Amestris" 9999 1000 5000 (exact->inexact (/ 9999 1000))]
                                 ["Kamina City" 2000 9999 9999 (exact->inexact (/ 2000 9999))])))
    (check-equal? extended-world
                  (table-extend check-world [area] [total-area + area]))
    (check-equal? (table-reject [total-area] extended-world)
                  check-world))

  (check-equal? (table-select [name age] my-table)
                (make-table [name age]
                            ["James McAvoy"  30]
                            ["Matt Murdock"  35]
                            ["Shallan Davar" 20]))

  (check-equal? (table-select [name age] my-table)
                (make-table [age name]
                            [30  "James McAvoy"]
                            [35  "Matt Murdock"]
                            [20 "Shallan Davar"]))

  (check-equal? (table-filter my-table [president] (equal? president "Stick"))
                (make-table [timestamp    name            age president]
                            ["2016-01-02" "Matt Murdock"  35  "Stick"]
                            ["2016-01-03" "Shallan Davar" 20  "Stick"]))

  (check-equal? (table-order my-table [age descending])
                (make-table [timestamp    name            age president]
                            ["2016-01-02" "Matt Murdock"  35  "Stick"]
                            ["2016-01-01" "James McAvoy"  30  "Magneto"]
                            ["2016-01-03" "Shallan Davar" 20  "Stick"]))

  (check-equal? (table-column-ref 'name world)
                (list "Atlantis" "Amestris" "Kamina City"))

  (define emp (make-table [last-name department-id]
                          ["Rafferty" 31]
                          ["Jones" 33]
                          ["Heisenberg" 33]
                          ["Robinson" 34]
                          ["Smith" 34]
                          ["Williams" #f]))

  (define dept (make-table [department-id department-name]
                           [31 "Sales"]
                           [33 "Engineering"]
                           [34 "Clerical"]
                           [35 "Marketing"]))

  (check-equal? (table-cross-join emp (table-rename dept [d.department-id department-id]))
                (make-table [last-name department-id d.department-id department-name]
                            ["Rafferty" 31 31 "Sales"]
                            ["Rafferty" 31 33 "Engineering"]
                            ["Rafferty" 31 34 "Clerical"]
                            ["Rafferty" 31 35 "Marketing"]
                            ["Jones" 33 31 "Sales"]
                            ["Jones" 33 33 "Engineering"]
                            ["Jones" 33 34 "Clerical"]
                            ["Jones" 33 35 "Marketing"]
                            ["Heisenberg" 33 31 "Sales"]
                            ["Heisenberg" 33 33 "Engineering"]
                            ["Heisenberg" 33 34 "Clerical"]
                            ["Heisenberg" 33 35 "Marketing"]
                            ["Robinson" 34 31 "Sales"]
                            ["Robinson" 34 33 "Engineering"]
                            ["Robinson" 34 34 "Clerical"]
                            ["Robinson" 34 35 "Marketing"]
                            ["Smith" 34 31 "Sales"]
                            ["Smith" 34 33 "Engineering"]
                            ["Smith" 34 34 "Clerical"]
                            ["Smith" 34 35 "Marketing"]
                            ["Williams" #f 31 "Sales"]
                            ["Williams" #f 33 "Engineering"]
                            ["Williams" #f 34 "Clerical"]
                            ["Williams" #f 35 "Marketing"]))

  (let ((emp+dept-expected (make-table [last-name department-id department-name]
                                       ["Rafferty" 31 "Sales"]
                                       ["Jones" 33 "Engineering"]
                                       ["Heisenberg" 33 "Engineering"]
                                       ["Robinson" 34 "Clerical"]
                                       ["Smith" 34 "Clerical"])))
    (check-equal? (table-equi-join emp (table-rename dept [d.department-id department-id])
                                   [department-id d.department-id])
                  emp+dept-expected)
    (check-equal? (table-natural-join emp dept)
                  emp+dept-expected))
  )
