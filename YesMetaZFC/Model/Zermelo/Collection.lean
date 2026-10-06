import YesMetaZFC.Model.Zermelo.Scope
import YesMetaZFC.Model.Zermelo.Project

/-! # 原收集模式的局部范围分配
关系正文、前件输入、结论输入、候选见证、容器分别使用 R、I、J、W、E。
构造 B = {y ∈ W | ¬¬∃x ∈ I∩a, φᴿ(x,y)}，并要求 P(W)⊆E。
结论中的 x∈a guard 把 J 中的实际输入交回 I，不要求 J⊆W。
公式仍由仓库原收集模式翻译得到，本层不声称整个原推导均可采用这一分配。
-/

namespace YesMetaZFC.Model.Zermelo
open Logic Logic.FirstOrder SetTheory SetTheory.Definitional
universe u
attribute [local implicit_reducible] SetTheory.signature

private theorem sc_tf {b f s} (t : FirstOrder.Term ℒ b f s) (ρ : Env.{u} b f) (d : V.{u}) :
    (t.weakenFree SetSort.set).eval (ρ.pushFree d) = t.eval ρ :=
  tm_rename t _ _ _ _ (fun _ => rfl) (fun _ => rfl)

private theorem sc_ptm {n m} (t : Project.Term n) (hc : t.freeSupport = [])
    (θ : Fin n → Project.Term m) (ht : ∀ i, (θ i).freeSupport = [])
    (ρ : Env.{u} (Project.fo_bound_context m) []) (τ : Env.{u} (Project.fo_bound_context n) [])
    (h : ∀ i, (Project.fo_term (θ i) (ht i)).eval ρ = τ.boundVal (Project.fo_bound_variable i)) :
    (Project.fo_term (t.bind θ) ((Term.freeSupport_bind_of_closed θ ht t).trans hc)).eval ρ =
      (Project.fo_term t hc).eval τ := by
  cases t with
  | bound i => exact h i
  | free _ => cases hc

private theorem sc_pw {n} (t : Project.Term n) (hc : t.freeSupport = [])
    (ρ : Env.{u} (Project.fo_bound_context n) []) (x : V.{u}) :
    (Project.fo_term t.weaken ((Term.freeSupport_weaken t).trans hc)).eval (ρ.pushBound x) =
      (Project.fo_term t hc).eval ρ := by
  cases t with
  | bound _ => rfl
  | free _ => cases hc

/-- 原模式的代入律：固定范围，仅改变公式原有的变量。 -/
theorem sc_pbind {s n m} (φ : Project.Formula s n) (hc : φ.FreeClosed)
    (θ : Fin n → Project.Term m) (ht : ∀ i, (θ i).freeSupport = []) (d : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context m) []) (τ : Env.{u} (Project.fo_bound_context n) [])
    (h : ∀ i, (Project.fo_term (θ i) (ht i)).eval ρ = τ.boundVal (Project.fo_bound_variable i)) :
    sc_sat (Project.fo_formula (φ.bind θ)
      ((Definitional.Formula.freeClosed_bind_iff_of_closed θ ht φ).mpr hc)) d ρ ↔
      sc_sat (Project.fo_formula φ hc) d τ := by
  induction φ generalizing m with
  | falsum | truth => exact Iff.rfl
  | mem t t' =>
    exact (sat_weaken (s := SetSort.set) (.rel .membership (.cons (Project.fo_term (t.bind θ)
        ((Term.freeSupport_bind_of_closed θ ht t).trans hc.1)) (.cons (Project.fo_term (t'.bind θ)
        ((Term.freeSupport_bind_of_closed θ ht t').trans hc.2)) .nil))) ρ d).trans
      ((sat_mem _ _ _).trans ((sc_ptm t hc.1 θ ht ρ τ h) ▸
        (sc_ptm t' hc.2 θ ht ρ τ h) ▸ (sat_mem _ _ _).symm.trans
          (sat_weaken (s := SetSort.set) (Project.fo_formula (.mem t t') hc) τ d).symm))
  | atom r _ ts =>
    have kc := (TermVector.freeClosed_bind_iff_of_closed θ ht ts).mpr hc
    have e i : (Project.fo_term ((ts.bind θ) i) (kc i)).eval ρ =
        (Project.fo_term (ts i) (hc i)).eval τ := by
      simpa only [TermVector.get_bind] using sc_ptm (ts i) (hc i) θ ht ρ τ h
    cases r with
    | extensionalEq =>
      exact (sat_weaken (s := SetSort.set) (.equal (Project.fo_term ((ts.bind θ) 0) (kc 0))
        (Project.fo_term ((ts.bind θ) 1) (kc 1))) ρ d).trans
        ((sat_eq _ _ _).trans ((e 0) ▸ (e 1) ▸ (sat_eq _ _ _).symm.trans
          (sat_weaken (s := SetSort.set) (Project.fo_formula (.atom .extensionalEq _ ts) hc) τ d).symm))
    | subset =>
      have k x i : (((Project.fo_term ((ts.bind θ) i) (kc i)).weakenBound SetSort.set).weakenFree
          SetSort.set).eval ((ρ.pushBound x).pushFree d) =
          (((Project.fo_term (ts i) (hc i)).weakenBound SetSort.set).weakenFree
            SetSort.set).eval ((τ.pushBound x).pushFree d) := by
        exact (sc_tf _ _ d).trans
          ((tm_weaken _ ρ x).trans ((e i).trans ((tm_weaken _ τ x).symm.trans
            (sc_tf _ _ d).symm)))
      exact ⟨fun p x hx q => (sat_mem _ _ _).mpr ((k x 1).symm ▸ (sat_mem _ _ _).mp
          (p x hx ((sat_mem _ _ _).mpr ((k x 0) ▸ (sat_mem _ _ _).mp q)))),
        fun p x hx q => (sat_mem _ _ _).mpr ((k x 1) ▸ (sat_mem _ _ _).mp
          (p x hx ((sat_mem _ _ _).mpr ((k x 0).symm ▸ (sat_mem _ _ _).mp q))))⟩
  | neg _ ih => exact not_congr (ih hc θ ht _ _ h)
  | conj _ _ ih ik => exact and_congr (ih hc.1 θ ht _ _ h) (ik hc.2 θ ht _ _ h)
  | disj _ _ ih ik => exact nn_congr (or_congr (ih hc.1 θ ht _ _ h) (ik hc.2 θ ht _ _ h))
  | imp _ _ ih ik => exact imp_congr (ih hc.1 θ ht _ _ h) (ik hc.2 θ ht _ _ h)
  | iff _ _ ih ik => exact st_iff_congr (ih hc.1 θ ht _ _ h) (ik hc.2 θ ht _ _ h)
  | forallE φ ih | existsE φ ih =>
    have e x := ih hc (Term.liftSubstitution θ) (Term.liftSubstitution_closed θ ht)
      (ρ.pushBound x) (τ.pushBound x) (fun i =>
        fin_cases rfl (fun i => (sc_pw (θ i) (ht i) ρ x).trans (h i)) i)
    first
    | exact ⟨fun p x hx => (e x).mp (p x hx), fun p x hx => (e x).mpr (p x hx)⟩
    | exact nn_congr ⟨fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mp p⟩,
        fun ⟨x, hx, p⟩ => ⟨x, hx, (e x).mpr p⟩⟩

/-- 首个自由变量限定见证，第二个自由变量限定关系正文。 -/
def sc_witness {b f} (φ : FirstOrder.Formula ℒ b f) : FirstOrder.Formula ℒ b (.set :: .set :: f) := by
  let z := (gl_form φ).weakenFree SetSort.set
  cases φ with
  | existsE s p =>
    cases s
    exact .existsE .set (.conj
      (.rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil)))
      ((gl_form p).weakenFree SetSort.set))
  | _ => exact z

/-- 五个范围参数依次为 E、J、I、W、R；前件读取 I，结论读取 J。 -/
def sc_input {b f} (post : Bool) (φ : FirstOrder.Formula ℒ b f) :
    FirstOrder.Formula ℒ b (.set :: .set :: .set :: .set :: .set :: f) := by
  let z := ((((gl_form φ).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
  cases φ with
  | forallE s p =>
    cases s
    cases p with
    | imp p q =>
      exact .forallE .set (.imp
        (.rel .membership (.cons (.bvar .here)
          (.cons (.fvar (if post then .there .here else .there (.there .here))) .nil)))
        (.imp ((((gl_form p).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set |>.weakenFree SetSort.set)
          (((sc_witness q).weakenFree SetSort.set).weakenFree SetSort.set |>.weakenFree SetSort.set)))
    | _ => exact z
  | _ => exact z

/-- 只扩大存在见证的范围，关系正文及其参数保持原样。 -/
theorem sc_witness_up {b f} (φ : FirstOrder.Formula ℒ b f) (r w v : V.{u})
    (h : V.sub w v) (ρ : Env.{u} b f) :
    sat (sc_witness φ) ((ρ.pushFree r).pushFree w) →
      sat (sc_witness φ) ((ρ.pushFree r).pushFree v) := by
  have k := (sat_weaken (s := SetSort.set) (gl_form φ) (ρ.pushFree r) w).trans
    (sat_weaken (s := SetSort.set) (gl_form φ) (ρ.pushFree r) v).symm
  cases φ with
  | existsE s p =>
    cases s
    exact fun hp => st_use hp (fun ⟨y, hy, hp⟩ => nn_in ⟨y, h y hy,
      (sat_weaken (s := SetSort.set) (gl_form p) ((ρ.pushBound y).pushFree r) v).mpr
        ((sat_weaken (s := SetSort.set) (gl_form p) ((ρ.pushBound y).pushFree r) w).mp hp)⟩)
  | _ => exact k.mp

private theorem sc_extra {b f} (φ : FirstOrder.Formula ℒ b f) (ρ : Env.{u} b f) (a c d : V.{u}) :
    sat (((φ.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set)
      (((ρ.pushFree a).pushFree c).pushFree d) ↔ sat φ ρ :=
  (sat_weaken ((φ.weakenFree SetSort.set).weakenFree SetSort.set) ((ρ.pushFree a).pushFree c) d).trans
    ((sat_weaken (φ.weakenFree SetSort.set) (ρ.pushFree a) c).trans (sat_weaken φ ρ a))

private theorem sc_four {b f} (φ : FirstOrder.Formula ℒ b f) (ρ : Env.{u} b f) (a c d e : V.{u}) :
    sat ((((φ.weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set)
      ((((ρ.pushFree a).pushFree c).pushFree d).pushFree e) ↔ sat φ ρ :=
  (sc_extra (φ.weakenFree SetSort.set) (ρ.pushFree a) c d e).trans (sat_weaken φ ρ a)

/-- 两个输入范围和正文范围固定时，扩大候选范围保持整个收集前件或结论。 -/
theorem sc_input_up {b f} (post : Bool) (φ : FirstOrder.Formula ℒ b f) (r i j w v e : V.{u})
    (h : V.sub w v) (ρ : Env.{u} b f) :
    sat (sc_input post φ) (((((ρ.pushFree r).pushFree w).pushFree i).pushFree j).pushFree e) →
      sat (sc_input post φ) (((((ρ.pushFree r).pushFree v).pushFree i).pushFree j).pushFree e) := by
  have k := (sc_four (gl_form φ) (ρ.pushFree r) w i j e).trans
    (sc_four (gl_form φ) (ρ.pushFree r) v i j e).symm
  cases φ with
  | forallE s p =>
    cases s
    cases p with
    | imp p q =>
      cases post
      all_goals
        intro hp x hx hq
        have e' := (sc_four (gl_form p) ((ρ.pushBound x).pushFree r) w i j e).mpr
          ((sc_four (gl_form p) ((ρ.pushBound x).pushFree r) v i j e).mp hq)
        exact (sc_extra (sc_witness q) (((ρ.pushBound x).pushFree r).pushFree v) i j e).mpr
          (sc_witness_up q r w v h (ρ.pushBound x)
            ((sc_extra (sc_witness q) (((ρ.pushBound x).pushFree r).pushFree w) i j e).mp
              (hp x hx e')))
    | _ => exact k.mp
  | _ => exact k.mp

/-- 容器在 E 中，容器的输入全称量词使用 J。 -/
def sc_result {b f} (φ : FirstOrder.Formula ℒ b f) :
    FirstOrder.Formula ℒ b (.set :: .set :: .set :: .set :: .set :: f) := by
  let z := ((((gl_form φ).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
  cases φ with
  | existsE s p =>
    cases s
    exact .existsE .set (.conj
      (.rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil))) (sc_input true p))
  | _ => exact z

/-- 输入集合来自 I；其成员从 I 收集，结论可以在另一个输入范围 J 上使用。 -/
def sc_core {b f} (φ : FirstOrder.Formula ℒ b f) :
    FirstOrder.Formula ℒ b (.set :: .set :: .set :: .set :: .set :: f) := by
  let z := ((((gl_form φ).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
  cases φ with
  | forallE s p =>
    cases s
    cases p with
    | imp p q =>
      cases q with
      | existsE s q =>
        cases s
        exact .forallE .set (.imp
          (.rel .membership (.cons (.bvar .here) (.cons (.fvar (.there (.there .here))) .nil)))
          (.imp (sc_input false p) (sc_result (.existsE .set q))))
      | _ => exact z
    | _ => exact z
  | _ => exact z

/-- 原收集核心的实际语法像，没有改写模式正文。 -/
def sc_collection {n} (φ : Project.BinarySchema n) :
    FirstOrder.Formula ℒ (Project.fo_bound_context n) [.set, .set, .set, .set, .set] :=
  sc_core (Project.fo_formula (Axioms.Schema.collectionCore φ) (Axioms.Schema.collection_core_closed φ))

/-- 保留全部候选的实际集合；正文解释与候选范围相互独立。 -/
def sc_collect {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) : V.{u} :=
  V.sep w (fun y => ¬¬∃ x, x ∈ i ∧ x ∈ a ∧
    sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y))

theorem sc_collect_mem {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a y : V.{u}) :
    y ∈ sc_collect φ r i w ρ a ↔ y ∈ w ∧ ¬¬∃ x, x ∈ i ∧ x ∈ a ∧
      sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y) :=
  V.sep_mem w y _ (fun e h => st_use h (fun ⟨x, hx, ha, hr⟩ => nn_in ⟨x, hx, ha,
    (sat_congr (gl_form (Project.fo_formula φ.body φ.freeClosed))
      (ρ := (((ρ.pushBound x).pushBound _).pushFree r))
      (τ := (((ρ.pushBound x).pushBound _).pushFree r))
      ⟨(fun j => match j with | .here => e | .there _ => V.eq_refl _),
        fun _ => V.eq_refl _⟩).mp hr⟩))

theorem sc_collect_bound {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) :
    sc_collect φ r i w ρ a ∈ V.power w :=
  (V.power_mem _ _).mpr (fun y hy => ((sc_collect_mem φ r i w ρ a y).mp hy).1)

/-- 交付同一个已构造的池中的见证，不在使用处重新建立整个收集对象。 -/
theorem sc_collect_use {n} (φ : Project.BinarySchema n) (r i w : V.{u})
    (ρ : Env.{u} (Project.fo_bound_context n) []) (a x : V.{u}) (hx : x ∈ i) (ha : x ∈ a)
    (h : ¬¬∃ y, y ∈ w ∧ sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y)) :
    ¬¬∃ y, y ∈ w ∧ y ∈ sc_collect φ r i w ρ a ∧
      sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y) :=
  st_use h (fun ⟨y, hy, hp⟩ => nn_in ⟨y, hy,
    (sc_collect_mem φ r i w ρ a y).mpr ⟨hy, nn_in ⟨x, hx, ha, hp⟩⟩, hp⟩)

/-- 输入和候选池可以扩张；正文范围 R 与全部源参数固定时，旧候选不会丢失。 -/
theorem sc_collect_mono {n} (φ : Project.BinarySchema n) (r i w i' w' : V.{u})
    (hi : V.sub i i') (hw : V.sub w w') (ρ : Env.{u} (Project.fo_bound_context n) []) (a : V.{u}) :
    V.sub (sc_collect φ r i w ρ a) (sc_collect φ r i' w' ρ a) := by
  intro y hy
  have k := (sc_collect_mem φ r i w ρ a y).mp hy
  exact (sc_collect_mem φ r i' w' ρ a y).mpr ⟨hw y k.1,
    st_use k.2 (fun ⟨x, hx, ha, hr⟩ => nn_in ⟨x, hi x hx, ha, hr⟩)⟩

/-- 扩大结论输入范围所需的精确条件：真正满足 x∈a 的新输入仍在旧输入范围内。 -/
abbrev Sc_cover (i j : V.{u}) : Prop := ∀ a, a ∈ i → ∀ x, x ∈ j → x ∈ a → x ∈ i

set_option maxHeartbeats 500000 in
/-- 不要求 I⊆W 或 J⊆W；成员 guard 提供前后输入范围之间的实际交接。 -/
theorem sc_collection_valid {n} (φ : Project.BinarySchema n) (r i j w e : V.{u})
    (hi : Sc_cover i j) (he : V.sub (V.power w) e)
    (ρ : Env.{u} (Project.fo_bound_context n) []) :
    sat (sc_collection φ) (((((ρ.pushFree r).pushFree w).pushFree i).pushFree j).pushFree e) := by
  intro a ha h
  let c := sc_collect φ r i w ρ a
  have hc : c ∈ e := he _ (sc_collect_bound φ r i w ρ a)
  have e₁ x y := sc_pbind φ.body φ.freeClosed (.bound ∘ BoundEmbedding.binaryUnderOne)
    (fun _ => rfl) r (((ρ.pushBound a).pushBound x).pushBound y)
    ((ρ.pushBound x).pushBound y)
    (fun i => fin_cases rfl (fun i => fin_cases rfl (fun _ => rfl) i) i)
  have e₂ x y := sc_pbind φ.body φ.freeClosed (.bound ∘ BoundEmbedding.binaryUnderTwo)
    (fun _ => rfl) r ((((ρ.pushBound a).pushBound c).pushBound x).pushBound y)
    ((ρ.pushBound x).pushBound y)
    (fun i => fin_cases rfl (fun i => fin_cases rfl (fun _ => rfl) i) i)
  apply nn_in
  refine ⟨c, hc, ?_⟩
  intro x hx hxa
  have hxi := hi a ha x hx hxa
  have hp := (sc_extra _ ((((ρ.pushBound a).pushBound x).pushFree r).pushFree w) i j e).mp (h x hxi hxa)
  apply (sc_extra _ (((((ρ.pushBound a).pushBound c).pushBound x).pushFree r).pushFree w) i j e).mpr
  have hp : ¬¬∃ y, y ∈ w ∧ sc_sat (Project.fo_formula φ.body φ.freeClosed) r ((ρ.pushBound x).pushBound y) :=
    st_use hp (fun ⟨y, hy, hr⟩ => nn_in ⟨y, hy,
      (e₁ x y).mp ((sat_weaken _ ((((ρ.pushBound a).pushBound x).pushBound y).pushFree r) w).mp hr)⟩)
  exact st_use (sc_collect_use φ r i w ρ a x hxi hxa hp) (fun ⟨y, hy, hcy, k⟩ => nn_in ⟨y, hy, hcy,
      (sat_weaken (s := SetSort.set) _ (((((ρ.pushBound a).pushBound c).pushBound x).pushBound y).pushFree r) w).mpr
        ((e₂ x y).mpr k)⟩)

/-- 模式参数的闭合量词使用 E；输入集合 a 的量词由 sc_core 单独分配。 -/
def sc_prefix : Nat → {b f : SortContext ℒ} → FirstOrder.Formula ℒ b f →
    FirstOrder.Formula ℒ b (.set :: .set :: .set :: .set :: .set :: f)
  | 0, _, _, φ => sc_core φ
  | n+1, _, _, φ => by
    let z := ((((gl_form φ).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set).weakenFree SetSort.set
    cases φ with
    | forallE s p =>
      cases s
      exact .forallE .set (.imp
        (.rel .membership (.cons (.bvar .here) (.cons (.fvar .here) .nil))) (sc_prefix n p))
    | _ => exact z

private theorem sc_close {s n} (φ : Project.Formula s n) (hc : φ.FreeClosed) (k : Nat) (r i j w e : V.{u})
    (h : ∀ ρ : Env.{u} (Project.fo_bound_context n) [],
      sat (sc_prefix k (Project.fo_formula φ hc)) (((((ρ.pushFree r).pushFree w).pushFree i).pushFree j).pushFree e)) :
    sat (sc_prefix (n+k) (Project.fo_formula (Definitional.Formula.forallClosure n φ)
      ((Definitional.Formula.freeClosed_forallClosure φ).mpr hc)))
      (((((FirstOrder.Env.empty.pushFree r).pushFree w).pushFree i).pushFree j).pushFree e) := by
  induction n generalizing k with
  | zero => simpa only [Nat.zero_add, Definitional.Formula.forallClosure] using h FirstOrder.Env.empty
  | succ n ih =>
    have e := ih (.forallE φ) hc (k+1) (fun ρ x _ => h (ρ.pushBound x))
    simpa only [Nat.add_succ, Nat.succ_add, Definitional.Formula.forallClosure] using e

/-- 直接接收原收集公理的闭句翻译，含全部参数闭合量词。 -/
theorem sc_collection_closed {n} (φ : Project.BinarySchema n) (r i j w e : V.{u})
    (hi : Sc_cover i j) (he : V.sub (V.power w) e) :
    sat (sc_prefix n (Project.fo_sentence (Axioms.Schema.collection φ)))
      (((((FirstOrder.Env.empty.pushFree r).pushFree w).pushFree i).pushFree j).pushFree e) :=
  sc_close (Axioms.Schema.collectionCore φ) (Axioms.Schema.collection_core_closed φ) 0 r i j w e
    (sc_collection_valid φ r i j w e hi he)

/-- info: 'YesMetaZFC.Model.Zermelo.sc_collection_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_collection_valid
/-- info: 'YesMetaZFC.Model.Zermelo.sc_collection_closed' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_collection_closed
/-- info: 'YesMetaZFC.Model.Zermelo.sc_input_up' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_input_up
/-- info: 'YesMetaZFC.Model.Zermelo.sc_collect_mono' does not depend on any axioms -/
#guard_msgs in
#print axioms sc_collect_mono

end YesMetaZFC.Model.Zermelo
