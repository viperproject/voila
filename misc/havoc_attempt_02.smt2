; (set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea
(set-option :smt.mbqi true)
(set-option :model true)
(set-option :produce-models true)
(set-option :model.v2 true)
; (set-option :model.compact true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.relevancy 3)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
(set-option :sat.random_seed 0)
; (set-option :combined_solver.solver2_timeout 100)
; (set-option :smt.refine_inj_axioms false)

(declare-fun state (Int) Int)
(declare-fun cond (Int) Bool)
(declare-fun T (Int) Bool)

(declare-fun sk_n (Int) Int)
(declare-fun sk_m (Int) Int)

(define-fun constrain_skolem ((v Int) (w Int) (i Int)) Bool
  (or
    (= v w)
    (and
      (< (sk_n i) (sk_m i))
      (= v (sk_n i))
      (= w (sk_m i))
      (forall ((k Int)) (!
        (=> (and (<= (sk_n i) k) (< k (sk_m i))) (cond k))
        :pattern ((cond k)))))))

(define-fun constrain_exists ((v Int) (w Int) (i Int)) Bool
  (or
    (= v w)
    (exists ((n Int) (m Int))
      (and
        (< n m)
        (= v n)
        (= w m)
        (forall ((k Int)) (!
          (=> (and (<= n k) (< k m)) (cond k))
          :pattern ((cond k))))))))
        
(declare-const v Int)
(declare-const w Int)
        
(push)
  (assert (forall ((k Int)) (!
    (iff (not (= k v)) (cond k))
    :pattern ((cond k)))))
  (assert (constrain_skolem v w 0))
  (assert (not (= v w)))
  (check-sat)
(pop)

(push)
  (assert (forall ((k Int)) (!
    (iff (not (= k v)) (cond k))
    :pattern ((cond k)))))
  (assert (constrain_exists v w 0))
  (assert (not (= v w)))
  (check-sat)
(pop)