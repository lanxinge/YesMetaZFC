import YesMetaZFC.Model.SetTheory.DirectedSystem.Basic
import YesMetaZFC.Model.SetTheory.Internal.Quotient
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence

/-! # 定向系统的实际直接极限

先分离共同后继等价关系，再取规范商；极限关系可用任意一对代表读取。
各分量的规范映射由商投影限制得到。相容映射的唯一分解即直接极限泛性质。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Di_limit_d (A p T R q C S : M.Domain) : Prop where
  projection : Fn0_d A C q
  range : ∀ B, M.mem B C ↔ ∃ x, Rd_entry_d x B q
  kernel : ∀ x y B D, Rd_entry_d x B q → Rd_entry_d y D q → (B = D ↔ Di_eq_d T x y)
  relation : ∀ x y B D, Rd_entry_d x B q → Rd_entry_d y D q →
    (Rd_entry_d B D S ↔ Di_rel_d p T R x y)
  bounded : ∀ B D, Rd_entry_d B D S → M.mem B C ∧ M.mem D C
  graph : ∀ s, M.mem s S → ∃ B D, KPair_d M s B D

theorem di_limit_exists_l (hZF : M.Models ZF) {J L A p T R : M.Domain}
    (h : Di_system_d J L A p T R) : ∃ q C S, Di_limit_d A p T R q C S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 1 := ⟨fun _ => T, fun _ => T⟩
  let φ : BinarySchema 1 := { body := di_eq_m (.bound 2) (.bound 1) .newest }
  obtain ⟨E, _, he⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have spec x y : Rd_entry_d x y E ↔ M.mem x A ∧ M.mem y A ∧ Di_eq_d T x y :=
    (he x y).trans (and_congr_right fun _ => and_congr_right fun _ => di_eq_sat_l hZF.1 _ _ _ _)
  have equiv : Qt_equiv_d A E := ⟨fun x hx => (spec x x).mpr ⟨hx, hx, h.eq_refl_l hx⟩,
    fun x y hxy => (spec y x).mpr (by obtain ⟨hx, hy, he⟩ := (spec x y).mp hxy; exact ⟨hy, hx, he.symm_l⟩),
    fun x y z hxy hyz => (spec x z).mpr ⟨((spec x y).mp hxy).1, ((spec y z).mp hyz).2.1,
      h.eq_trans_l ((spec x y).mp hxy).2.2 ((spec y z).mp hyz).2.2⟩⟩
  obtain ⟨q, C, hq⟩ := qt_map_exists_l hZF A E
  have kernel x y B D (hx : Rd_entry_d x B q) (hy : Rd_entry_d y D q) : B = D ↔ Di_eq_d T x y :=
    (hq.kernel_l hZF.1 equiv hx hy).trans ((spec x y).trans
      ⟨fun hh => hh.2.2, fun hh => ⟨(hq.function.bound_l hx).1, (hq.function.bound_l hy).1, hh⟩⟩)
  let η := (((⟨fun _ => q, fun _ => q⟩ : Env M 1).push p).push T).push R
  let ψ : BinarySchema 4 := { body := .existsE (.existsE (.conj
    (rd_entry_m (.bound 1) (.bound 3) (.bound 7)) (.conj
      (rd_entry_m .newest (.bound 2) (.bound 7))
      (di_rel_m (.bound 6) (.bound 5) (.bound 4) (.bound 1) .newest)))) }
  have sat B D : ψ.denote η B D ↔ ∃ x y, Rd_entry_d x B q ∧ Rd_entry_d y D q ∧ Di_rel_d p T R x y := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1, di_rel_sat_l hZF.1]; rfl
  obtain ⟨S, hS, hs⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η C
  refine ⟨q, C, S, hq.function, hq.range, kernel, fun x y B D hx hy => ?_,
    fun B D hBD => ⟨((hs B D).mp hBD).1, ((hs B D).mp hBD).2.1⟩, hS.1⟩
  exact (hs B D).trans ((and_congr_right fun _ => and_congr_right fun _ => sat B D).trans
      ⟨fun ⟨_, _, a, b, ha, hb, hab⟩ => (h.rel_congr_l ((kernel a x B B ha hx).mp rfl)
          ((kernel b y D D hb hy).mp rfl)).mp hab,
        fun hxy => ⟨(hq.function.bound_l hx).2, (hq.function.bound_l hy).2, x, y, hx, hy, hxy⟩⟩)

/-- 规范投影在每个分量上是关系嵌入，并与全部过渡映射交换。 -/
theorem di_stage_l (hZF : M.Models ZF) {J L A p T R q C S : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S) (i : M.Domain) :
    ∃ B j, (∀ x, M.mem x B ↔ M.mem x A ∧ Rd_entry_d x i p) ∧ Fn0_d B C j ∧
      (∀ x y, Rd_entry_d x y j ↔ M.mem x B ∧ Rd_entry_d x y q) ∧
      (∀ x y z, Rd_entry_d x z j → Rd_entry_d y z j → x = y) ∧
      ∀ x y u v, Rd_entry_d x u j → Rd_entry_d y v j → (Rd_entry_d u v S ↔ Rd_entry_d x y R) := by
  let φ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨B, hB⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases i (fun _ => p), fun _ => A⟩ A
  have spec x : M.mem x B ↔ M.mem x A ∧ Rd_entry_d x i p :=
    (hB x).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  obtain ⟨j, hj⟩ := ZF.exists_restriction hZF (kp_pair_l (ZF.modelsKP hZF)) q B
  have fn := hj.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hq.projection)
    (fun x hx => ((spec x).mp hx).1)
  have idx x u (hx : Rd_entry_d x u j) := ((spec x).mp ((hj.2 x u).mp hx).1).2
  refine ⟨B, j, spec, fn0_of_function_l (ZF.modelsKP hZF) fn, hj.2, ?_, ?_⟩
  · intro x y z hx hy
    exact (h.eq_at_l (idx x z hx) (idx y z hy)).mp
      ((hq.kernel x y z z ((hj.2 x z).mp hx).2 ((hj.2 y z).mp hy).2).mp rfl)
  · intro x y u v hx hy
    exact (hq.relation x y u v ((hj.2 x u).mp hx).2 ((hj.2 y v).mp hy).2).trans
      (h.rel_at_l (idx x u hx) (idx y v hy) (h.identity x (h.index.bound_l (idx x u hx)).1)
        (h.identity y (h.index.bound_l (idx y v hy)).1))

theorem Di_limit_d.commute_l {J L A p T R q C S x y B D : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S)
    (hxy : Rd_entry_d x y T) (hx : Rd_entry_d x B q) (hy : Rd_entry_d y D q) : B = D :=
  (hq.kernel x y B D hx hy).mpr ⟨y, hxy, h.identity y (h.bound x y hxy).2⟩

/-- 极限的集合论泛性质：给定任意相容的内部映射族，自动构造唯一分解图。 -/
theorem di_factor_l (hZF : M.Models ZF) {J L A p T R q C S Y f : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S) (hf : Fn0_d A Y f)
    (hc : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  apply qt_descend_l hZF hq.projection (fun B hB => (hq.range B).mp hB) hf
  intro x y B u v hx hy hxu hyv
  obtain ⟨z, hxz, hyz⟩ := (hq.kernel x y B B hx hy).mp rfl
  obtain ⟨w, _, hzw⟩ := hf.2.1 z (h.bound x z hxz).2
  exact (hc x z u w hxz hxu hzw).trans (hc y z v w hyz hyv hzw).symm

/-- 相容的关系保持映射族在极限上唯一分解为关系保持映射。 -/
theorem di_factor_rel_l (hZF : M.Models ZF) {J L A p T R q C S Y V f : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S) (hf : Fn0_d A Y f)
    (hc : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v)
    (hr : ∀ x y i u v, Rd_entry_d x i p → Rd_entry_d y i p →
      Rd_entry_d x u f → Rd_entry_d y v f → Rd_entry_d x y R → Rd_entry_d u v V) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      (∀ B D u v, Rd_entry_d B D S → Rd_entry_d B u g → Rd_entry_d D v g → Rd_entry_d u v V) ∧
      ∀ k, Fn0_d C Y k → (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y k) → k = g := by
  obtain ⟨g, hg, law, unique⟩ := di_factor_l hZF h hq hf hc
  refine ⟨g, hg, law, ?_, unique⟩
  intro B D u v hBD hBu hDv
  obtain ⟨x, hx⟩ := (hq.range B).mp (hg.bound_l hBu).1
  obtain ⟨y, hy⟩ := (hq.range D).mp (hg.bound_l hDv).1
  obtain ⟨i, a, b, ha, hb, hxa, hyb, hab⟩ := (hq.relation x y B D hx hy).mp hBD
  obtain ⟨u', _, hau⟩ := hf.2.1 a (h.bound x a hxa).2
  obtain ⟨v', _, hbv⟩ := hf.2.1 b (h.bound y b hyb).2
  obtain ⟨s, _, hxs⟩ := hf.2.1 x (hq.projection.bound_l hx).1
  obtain ⟨t, _, hyt⟩ := hf.2.1 y (hq.projection.bound_l hy).1
  have fn := fn0_function_l (ZF.modelsKP hZF) hg
  have eu : u' = u := (hc x a s u' hxa hxs hau).symm.trans (fn.1.2 B s u (law x B s hx hxs) hBu)
  have ev : v' = v := (hc y b t v' hyb hyt hbv).symm.trans (fn.1.2 D t v (law y D t hy hyt) hDv)
  exact eu ▸ ev ▸ hr a b i u' v' ha hb hau hbv hab

/-- 非空系统的极限自动获得统一满足关系所需的实际结构码。 -/
theorem di_model_exists_l (hZF : M.Models ZF) {J L A p T R : M.Domain}
    (h : Di_system_d J L A p T R) (hne : ∃ x, M.mem x A) :
    ∃ c q C S, Di_limit_d A p T R q C S ∧ Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c C S := by
  obtain ⟨q, C, S, hq⟩ := di_limit_exists_l hZF h
  obtain ⟨a, ha⟩ := hne
  obtain ⟨B, hB, _⟩ := hq.projection.2.1 a ha
  obtain ⟨c, hc⟩ := (kp_pair_l (ZF.modelsKP hZF)).total C S
  exact ⟨c, q, C, S, hq, hc, ⟨B, hB⟩, hq.graph, hq.bounded⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 实际定向系统及其直接极限的一阶编码

公式逐项保留原图的函子律、投影核与极限关系，用于内部递归收集真实超幂。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def di_order_m {d} (J L : Term d) : Formula 1 d := set[d] ⟪
  (∀ i ∈ ⌜J⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜L⌝ₛ)) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜L⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, k, ⌜L⌝ₛ)) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) → i ∈ ⌜J⌝ₛ ∧ j ∈ ⌜J⌝ₛ) ∧
  (∀ i ∈ ⌜J⌝ₛ, ∀ j ∈ ⌜J⌝ₛ, ∃ k ∈ ⌜J⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, k, ⌜L⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(j, k, ⌜L⌝ₛ))⟫
derive_free_closed di_order_m

theorem di_order_sat_l (hE : Extensional M) {d} (η : Env M d) (J L : Term d) :
    Formula.satisfies η (di_order_m J L) ↔ Di_order_d (J.eval η) (L.eval η) := by
  simp only [di_order_m, Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨r, t, b, d⟩ => ⟨r, t, b, fun i j hi hj => d i hi j hj⟩,
    fun h => ⟨h.refl, h.trans, h.bound, fun i hi j hj => h.directed i j hi hj⟩⟩

def di_system_m {d} (J L A p T R : Term d) : Formula 1 d := set[d] ⟪
  ⌜di_order_m⌝ₚ(⌜J⌝ₛ, ⌜L⌝ₛ) ∧ ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜J⌝ₛ, ⌜p⌝ₛ) ∧
  (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → x ∈ ⌜A⌝ₛ ∧ y ∈ ⌜A⌝ₛ) ∧
  (∀ x y i j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ)) ∧
  (∀ x ∈ ⌜A⌝ₛ, ⌜rd_entry0_m⌝ₚ(x, x, ⌜T⌝ₛ)) ∧
  (∀ x y z, ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, z, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ)) ∧
  (∀ x i j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, j, ⌜L⌝ₛ) →
    ∃ y, ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ)) ∧
  (∀ x y z j, ⌜rd_entry0_m⌝ₚ(y, j, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(z, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, y, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ) → y = z) ∧
  (∀ x y z i, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, z, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, z, ⌜T⌝ₛ) → x = y) ∧
  (∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, ⌜R⌝ₛ) → ∃ i, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ)) ∧
  (∀ x y i u v j, ⌜rd_entry0_m⌝ₚ(x, i, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, i, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(u, j, ⌜p⌝ₛ) → ⌜rd_entry0_m⌝ₚ(v, j, ⌜p⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(x, u, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, v, ⌜T⌝ₛ) →
    (⌜rd_entry0_m⌝ₚ(x, y, ⌜R⌝ₛ) ↔ ⌜rd_entry0_m⌝ₚ(u, v, ⌜R⌝ₛ)))⟫
derive_free_closed di_system_m

theorem di_system_sat_l (hE : Extensional M) {d} (η : Env M d) (J L A p T R : Term d) :
    Formula.satisfies η (di_system_m J L A p T R) ↔
      Di_system_d (J.eval η) (L.eval η) (A.eval η) (p.eval η) (T.eval η) (R.eval η) := by
  simp only [di_system_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_iff_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    rd_entry0_sat_l hE, fn0_sat_l hE, di_order_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, k⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k⟩,
    fun h => ⟨h.order, h.index, h.bound, h.forward, h.identity, h.comp, h.total, h.unique, h.injective, h.locality, h.relation⟩⟩

def di_limit_m {d} (A p T R q C S : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜A⌝ₛ, ⌜C⌝ₛ, ⌜q⌝ₛ) ∧ (∀ B, B ∈ ⌜C⌝ₛ ↔ ∃ x, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ)) ∧
  (∀ x y B D, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, D, ⌜q⌝ₛ) → (B = D ↔ ⌜di_eq_m⌝ₚ(⌜T⌝ₛ, x, y))) ∧
  (∀ x y B D, ⌜rd_entry0_m⌝ₚ(x, B, ⌜q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(y, D, ⌜q⌝ₛ) →
    (⌜rd_entry0_m⌝ₚ(B, D, ⌜S⌝ₛ) ↔ ⌜di_rel_m⌝ₚ(⌜p⌝ₛ, ⌜T⌝ₛ, ⌜R⌝ₛ, x, y))) ∧
  (∀ B D, ⌜rd_entry0_m⌝ₚ(B, D, ⌜S⌝ₛ) → B ∈ ⌜C⌝ₛ ∧ D ∈ ⌜C⌝ₛ) ∧
  ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜S⌝ₛ)⟫
derive_free_closed di_limit_m

theorem di_limit_sat_l (hE : Extensional M) {d} (η : Env M d) (A p T R q C S : Term d) :
    Formula.satisfies η (di_limit_m A p T R q C S) ↔
      Di_limit_d (A.eval η) (p.eval η) (T.eval η) (R.eval η) (q.eval η) (C.eval η) (S.eval η) := by
  simp only [di_limit_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_forallMem_iff, kpair_sat_l M hE,
    rd_entry0_sat_l hE, fn0_sat_l hE, di_eq_sat_l hE, di_rel_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
    fun h => ⟨h.projection, h.range, h.kernel, h.relation, h.bounded, h.graph⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 直接极限的内部良基性

共同后继关系在带标号载体上的良基性与商上的良基性等价，只需 ZF。
可数定向系统的良基分量在 ZF＋DC 下有良基极限；普通有限定向性不足。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

/-- 每个内部可数指标族都有共同上界。 -/
def Di_sigma_d (ω J L : M.Domain) : Prop := ∀ f, Fn0_d ω J f →
  ∃ k, M.mem k J ∧ ∀ n i, Rd_entry_d n i f → Rd_entry_d i k L

theorem di_sigma_of_top_l {ω J L k : M.Domain} (hk : M.mem k J)
    (ht : ∀ i, M.mem i J → Rd_entry_d i k L) : Di_sigma_d ω J L :=
  fun _ hf => ⟨k, hk, fun _ _ hi => ht _ (hf.bound_l hi).2⟩

/-- 各分量的内部良基性，以同一指标的实际子集表达。 -/
def Di_wf_d (A p R : M.Domain) : Prop := ∀ i B, M.MemberSubset B A →
  (∀ x, M.mem x B → Rd_entry_d x i p) → (∃ x, M.mem x B) →
    ∃ x, M.mem x B ∧ ∀ y, M.mem y B → ¬ Rd_entry_d y x R

/-- 可数定向性把一条下降链同时送到一个分量；不对外部自然数归纳。 -/
theorem di_sigma_wf_l (hZF : M.Models ZF) {ω J L A p T R q C S : M.Domain}
    (hω : M.IsOmega ω) (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω)
    (h : Di_system_d J L A p T R) (hs : Di_sigma_d ω J L) (hw : Di_wf_d A p R)
    (hq : Di_limit_d A p T R q C S) : Wf_rel_d C S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push T).push R
  let φ : BinarySchema 3 := { body := di_rel_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, _, hp⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have hP x y : Rd_entry_d x y P ↔ M.mem x A ∧ M.mem y A ∧ Di_rel_d p T R x y :=
    (hp x y).trans (and_congr_right fun _ => and_congr_right fun _ => di_rel_sat_l hZF.1 _ _ _ _ _ _)
  apply (wf_quotient_l hZF hq.projection (fun B hB => (hq.range B).mp hB)
    (fun x y B D hx hy => (hq.relation x y B D hx hy).trans
      ⟨fun hxy => (hP x y).mpr ⟨(hq.projection.bound_l hx).1, (hq.projection.bound_l hy).1, hxy⟩,
        fun hxy => ((hP x y).mp hxy).2.2⟩)).mpr
  apply wf_of_no_desc_l hZF hDC
  intro f hf hd
  obtain ⟨v, hv⟩ := cp0_exists_l (ZF.modelsKP hZF) hf h.index
  obtain ⟨k, _, hk⟩ := hs v hv.1
  have bound n x (hnx : Rd_entry_d n x f) : ∃ y, Rd_entry_d y k p ∧ Rd_entry_d x y T := by
    obtain ⟨i, _, hxi⟩ := h.index.2.1 x (hf.bound_l hnx).2
    exact h.total x i k hxi (hk n i ((hv.value_l hf h.index hnx).mpr hxi))
  let ψ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF ψ ⟨Fin.cases k (fun _ => p), fun _ => A⟩ A
  have hB x : M.mem x B ↔ M.mem x A ∧ Rd_entry_d x k p :=
    (hb x).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  have wb : Wf_rel_d B R := fun Y hY hn => hw k Y (fun x hx => ((hB x).mp (hY x hx)).1)
    (fun x hx => ((hB x).mp (hY x hx)).2) hn
  let η := ((⟨fun _ => f, fun _ => f⟩ : Env M 1).push T).push B
  let χ : BinarySchema 3 := { body := .conj (.mem .newest (.bound 2)) (.existsE
    (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m .newest (.bound 1) (.bound 4)))) }
  have sat n y : χ.denote η n y ↔ M.mem y B ∧ ∃ x, Rd_entry_d n x f ∧ Rd_entry_d x y T := by
    simp only [χ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1]; rfl
  obtain ⟨g, hg, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I χ η (source := ω) (target := B)
    (fun n hn => by
      obtain ⟨x, _, hnx⟩ := hf.2.1 n hn
      obtain ⟨y, hyk, hxy⟩ := bound n x hnx
      exact ⟨y, (sat n y).mpr ⟨(hB y).mpr ⟨(h.index.bound_l hyk).1, hyk⟩, x, hnx, hxy⟩⟩)
    (fun n _ y z hy hz => by
      obtain ⟨hyB, x, hnx, hxy⟩ := (sat n y).mp hy
      obtain ⟨hzB, x', hnx', hxz⟩ := (sat n z).mp hz
      have e := (fn0_function_l (ZF.modelsKP hZF) hf).1.2 n x' x hnx' hnx
      exact h.unique x y z k ((hB y).mp hyB).2 ((hB z).mp hzB).2 hxy (e ▸ hxz))
    (fun n y _ hy => ((sat n y).mp hy).1)
  apply wf_no_desc_l hZF hω wb (fn0_of_function_l (ZF.modelsKP hZF) hg)
  intro n m y z hnm hny hmz
  obtain ⟨hyB, x, hnx, hxy⟩ := (sat n y).mp ((spec n y).mp hny).2
  obtain ⟨hzB, v, hmv, hvz⟩ := (sat m z).mp ((spec m z).mp hmz).2
  exact (h.rel_at_l ((hB z).mp hzB).2 ((hB y).mp hyB).2 hvz hxy).mp
    ((hP v x).mp (hd n m x v hnm hnx hmv)).2.2

/-- 相容锥的关系保持性沿泛性质下降；实际良基目标因而证明极限良基。 -/
theorem di_cone_wf_l (hZF : M.Models ZF) {J L A p T R q C S Y V f : M.Domain}
    (h : Di_system_d J L A p T R) (hq : Di_limit_d A p T R q C S)
    (hf : Fn0_d A Y f) (hw : Wf_rel_d Y V)
    (hc : ∀ x y u v, Rd_entry_d x y T → Rd_entry_d x u f → Rd_entry_d y v f → u = v)
    (hr : ∀ x y i u v, Rd_entry_d x i p → Rd_entry_d y i p →
      Rd_entry_d x u f → Rd_entry_d y v f → Rd_entry_d x y R → Rd_entry_d u v V) :
    ∃ g, Fn0_d C Y g ∧ (∀ x B y, Rd_entry_d x B q → Rd_entry_d x y f → Rd_entry_d B y g) ∧
      Wf_rel_d C S := by
  obtain ⟨g, hg, law, rel, _⟩ := di_factor_rel_l hZF h hq hf hc hr
  exact ⟨g, hg, law, wf_of_map_l hZF hw hg rel⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 在指标上递增的极限下降链

若极限关系不良基，DC 可把每个新节点放到同时容纳当前节点的后继分量。
这样整条下降链的指标递增，下一步的测度约束属于下一节点自己的分量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_step_d (p T S u v : M.Domain) : Prop := ∃ i w,
  Rd_entry_d v i p ∧ Rd_entry_d w i p ∧ Rd_entry_d u w T ∧ Rd_entry_d v w S
def di_step_m {d} (p T S u v : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (rd_entry_m v.weaken.weaken (.bound 1) p.weaken.weaken)
    (.conj (rd_entry_m .newest (.bound 1) p.weaken.weaken) (.conj
      (rd_entry_m u.weaken.weaken .newest T.weaken.weaken) (rd_entry_m v.weaken.weaken .newest S.weaken.weaken)))))
derive_free_closed di_step_m
theorem di_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p T S u v : Term d) :
    Formula.satisfies ρ (di_step_m p T S u v) ↔ Di_step_d (p.eval ρ) (T.eval ρ) (S.eval ρ) (u.eval ρ) (v.eval ρ) := by
  simp only [di_step_m, Di_step_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem di_wf_of_no_step_l (hZF : M.Models ZF) {ω J O A p T S q C R : M.Domain}
    (hDC : Dc_d (kp_pair_l (ZF.modelsKP hZF)) ω) (h : Di_system_d J O A p T S)
    (hq : Di_limit_d A p T S q C R)
    (hn : ∀ f, Fn0_d ω A f → ¬ (∀ i j u v, M.SuccessorOf j i →
      Rd_entry_d i u f → Rd_entry_d j v f → Di_step_d p T S u v)) : Wf_rel_d C R := by
  classical
  intro Y hY hne
  apply Classical.byContradiction
  intro hmin
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (rd_entry_m (.bound 1) .newest (.bound 3)) }
  obtain ⟨B, hb⟩ := ZF.separation_exists_d hZF φ ((⟨fun _ => q, fun _ => q⟩ : Env M 1).push Y) A
  have spec u : M.mem u B ↔ M.mem u A ∧ ∃ D, M.mem D Y ∧ Rd_entry_d u D q := by
    simpa only [φ, Formula.satisfies_existsMem_iff, rd_entry_sat_l hZF.1] using! hb u
  let ψ : BinarySchema 3 := { body := di_step_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨P, _, hp⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ
    (((⟨fun _ => p, fun _ => p⟩ : Env M 1).push T).push S) B
  have ps u v : Rd_entry_d u v P ↔ M.mem u B ∧ M.mem v B ∧ Di_step_d p T S u v :=
    (hp u v).trans (and_congr_right fun _ => and_congr_right fun _ => di_step_sat_l hZF.1 _ _ _ _ _ _)
  have serial u (hu : M.mem u B) : ∃ v, M.mem v B ∧ Rd_entry_d u v P := by
    obtain ⟨huA, D, hDY, huD⟩ := (spec u).mp hu
    have below : ∃ E, M.mem E Y ∧ Rd_entry_d E D R := by
      apply Classical.byContradiction
      intro hh
      exact hmin ⟨D, hDY, fun E hE hED => hh ⟨E, hE, hED⟩⟩
    obtain ⟨E, hEY, hED⟩ := below
    obtain ⟨v, hvE⟩ := (hq.range E).mp (hY E hEY)
    obtain ⟨i, w, z, hwi, hzi, hvw, huz, hwz⟩ := (hq.relation v u E D hvE huD).mp hED
    obtain ⟨F, _, hwF⟩ := hq.projection.2.1 w (h.bound v w hvw).2
    have eq := hq.commute_l h hvw hvE hwF
    have hwB := (spec w).mpr ⟨(h.bound v w hvw).2, F, eq ▸ hEY, hwF⟩
    exact ⟨w, hwB, (ps u w).mpr ⟨hu, hwB, i, z, hwi, hzi, huz, hwz⟩⟩
  obtain ⟨D, hDY⟩ := hne
  obtain ⟨u, huD⟩ := (hq.range D).mp (hY D hDY)
  obtain ⟨f, hf, _, step⟩ := hDC B P u ((spec u).mpr ⟨(hq.projection.bound_l huD).1, D, hDY, huD⟩) serial
  exact hn f ((fn0_of_function_l (ZF.modelsKP hZF) hf).mono_target_l fun v hv => ((spec v).mp hv).1)
    (fun i j u v hij hiu hjv => ((ps u v).mp (step i j u v hij hiu hjv)).2.2)

end YesMetaZFC.SetTheory.Internal

/-! ## 由实际相容嵌入族构造定向系统

一张标签图与一张共同目标中的取值图编码整个族。分量内取值单射、像随指标
增大而包含时，过渡图由相同取值唯一确定；无需另给恒等、复合或关系保持证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_cone_system_l (hZF : M.Models ZF) {J L A p Y V e : M.Domain}
    (ho : Di_order_d J L) (hp : Fn0_d A J p) (he : Fn0_d A Y e)
    (hinj : ∀ a b i x, Rd_entry_d a i p → Rd_entry_d b i p → Rd_entry_d a x e → Rd_entry_d b x e → a = b)
    (hmono : ∀ a i j x, Rd_entry_d a i p → Rd_entry_d i j L → Rd_entry_d a x e →
      ∃ b, Rd_entry_d b j p ∧ Rd_entry_d b x e) : ∃ T R,
      Di_system_d J L A p T R ∧
      (∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
        (Rd_entry_d a b T ↔ Rd_entry_d i j L ∧ x = y)) ∧
      ∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
        (Rd_entry_d a b R ↔ i = j ∧ Rd_entry_d x y V) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push e).push L
  let φ : BinarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (rd_entry_m (.bound 4) (.bound 2) (.bound 7)) (.conj
      (rd_entry_m (.bound 3) (.bound 1) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) .newest (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 2) (.bound 1) (.bound 5)))))))) }
  have sat a b : φ.denote ρ a b ↔ ∃ i j x, Rd_entry_d a i p ∧ Rd_entry_d b j p ∧
      Rd_entry_d a x e ∧ Rd_entry_d b x e ∧ Rd_entry_d i j L := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨T, _, ht⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have fp := fn0_function_l (ZF.modelsKP hZF) hp
  have fe := fn0_function_l (ZF.modelsKP hZF) he
  have ts a b i j x y (hai : Rd_entry_d a i p) (hbj : Rd_entry_d b j p)
      (hax : Rd_entry_d a x e) (hby : Rd_entry_d b y e) : Rd_entry_d a b T ↔ Rd_entry_d i j L ∧ x = y := by
    change M.PairMember I a b T ↔ _
    rw [ht a b, sat a b]
    constructor
    · rintro ⟨_, _, i', j', z, hai', hbj', haz, hbz, hij⟩
      exact ⟨fp.1.2 a i' i hai' hai ▸ fp.1.2 b j' j hbj' hbj ▸ hij,
        (fe.1.2 a z x haz hax).symm.trans (fe.1.2 b z y hbz hby)⟩
    · rintro ⟨hij, eq⟩
      exact ⟨(hp.bound_l hai).1, (hp.bound_l hbj).1, i, j, x, hai, hbj, hax, eq.symm ▸ hby, hij⟩
  let η := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push e).push V
  let ψ : BinarySchema 3 := { body := .existsE (.existsE (.existsE (.conj
    (rd_entry_m (.bound 4) (.bound 2) (.bound 7)) (.conj
      (rd_entry_m (.bound 3) (.bound 2) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) (.bound 1) (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 1) .newest (.bound 5)))))))) }
  have sat' a b : ψ.denote η a b ↔ ∃ i x y, Rd_entry_d a i p ∧ Rd_entry_d b i p ∧
      Rd_entry_d a x e ∧ Rd_entry_d b y e ∧ Rd_entry_d x y V := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨R, _, hr⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η A
  have rs a b i j x y (hai : Rd_entry_d a i p) (hbj : Rd_entry_d b j p)
      (hax : Rd_entry_d a x e) (hby : Rd_entry_d b y e) : Rd_entry_d a b R ↔ i = j ∧ Rd_entry_d x y V := by
    change M.PairMember I a b R ↔ _
    rw [hr a b, sat' a b]
    constructor
    · rintro ⟨_, _, k, u, v, hak, hbk, hau, hbv, huv⟩
      exact ⟨(fp.1.2 a k i hak hai).symm.trans (fp.1.2 b k j hbk hbj),
        fe.1.2 a u x hau hax ▸ fe.1.2 b v y hbv hby ▸ huv⟩
    · rintro ⟨eq, hxy⟩
      exact ⟨(hp.bound_l hai).1, (hp.bound_l hbj).1, i, x, y, hai, eq.symm ▸ hbj, hax, hby, hxy⟩
  have tb a b (hab : Rd_entry_d a b T) : M.mem a A ∧ M.mem b A :=
    ⟨((ht a b).mp hab).1, ((ht a b).mp hab).2.1⟩
  refine ⟨T, R, ⟨ho, hp, tb, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ts, rs⟩
  · intro a b i j hai hbj hab
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (hp.bound_l hbj).1
    exact ((ts a b i j x y hai hbj hax hby).mp hab).1
  · intro a ha
    obtain ⟨i, hi, hai⟩ := hp.2.1 a ha
    obtain ⟨x, _, hax⟩ := he.2.1 a ha
    exact (ts a a i i x x hai hai hax hax).mpr ⟨ho.refl i hi, rfl⟩
  · intro a b c hab hbc
    obtain ⟨i, _, hai⟩ := hp.2.1 a (tb a b hab).1
    obtain ⟨j, _, hbj⟩ := hp.2.1 b (tb a b hab).2
    obtain ⟨k, _, hck⟩ := hp.2.1 c (tb b c hbc).2
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a b hab).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb a b hab).2
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb b c hbc).2
    obtain ⟨hij, exy⟩ := (ts a b i j x y hai hbj hax hby).mp hab
    obtain ⟨hjk, eyz⟩ := (ts b c j k y z hbj hck hby hcz).mp hbc
    exact (ts a c i k x z hai hck hax hcz).mpr ⟨ho.trans i j k hij hjk, exy.trans eyz⟩
  · intro a i j hai hij
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨b, hbj, hbx⟩ := hmono a i j x hai hij hax
    exact ⟨b, hbj, (ts a b i j x x hai hbj hax hbx).mpr ⟨hij, rfl⟩⟩
  · intro a b c j hbj hcj hab hac
    obtain ⟨i, _, hai⟩ := hp.2.1 a (tb a b hab).1
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a b hab).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb a b hab).2
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb a c hac).2
    have ey := ((ts a b i j x y hai hbj hax hby).mp hab).2
    have ez := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    exact hinj b c j x hbj hcj (ey.symm ▸ hby) (ez.symm ▸ hcz)
  · intro a b c i hai hbi hac hbc
    obtain ⟨j, _, hcj⟩ := hp.2.1 c (tb a c hac).2
    obtain ⟨x, _, hax⟩ := he.2.1 a (tb a c hac).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (tb b c hbc).1
    obtain ⟨z, _, hcz⟩ := he.2.1 c (tb a c hac).2
    have ex := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    have ey := ((ts b c i j y z hbi hcj hby hcz).mp hbc).2
    exact hinj a b i z hai hbi (ex ▸ hax) (ey ▸ hby)
  · intro a b hab
    obtain ⟨i, _, _, hai, hbi, _⟩ := (sat' a b).mp ((hr a b).mp hab).2.2
    exact ⟨i, hai, hbi⟩
  · intro a b i c d j hai hbi hcj hdj hac hbd
    obtain ⟨x, _, hax⟩ := he.2.1 a (hp.bound_l hai).1
    obtain ⟨y, _, hby⟩ := he.2.1 b (hp.bound_l hbi).1
    obtain ⟨z, _, hcz⟩ := he.2.1 c (hp.bound_l hcj).1
    obtain ⟨w, _, hdw⟩ := he.2.1 d (hp.bound_l hdj).1
    have ex := ((ts a c i j x z hai hcj hax hcz).mp hac).2
    have ey := ((ts b d i j y w hbi hdj hby hdw).mp hbd).2
    have h₁ : Rd_entry_d a b R ↔ Rd_entry_d x y V :=
      (rs a b i i x y hai hbi hax hby).trans ⟨And.right, fun hr => ⟨rfl, hr⟩⟩
    have h₂ : Rd_entry_d c d R ↔ Rd_entry_d z w V :=
      (rs c d j j z w hcj hdj hcz hdw).trans ⟨And.right, fun hr => ⟨rfl, hr⟩⟩
    exact h₁.trans (by rw [ex, ey]; exact h₂.symm)

/-- 一个覆盖目标的单射相容锥已经实现了直接极限。 -/
theorem di_cone_limit_l {J L A p T R e Y V : M.Domain}
    (h : Di_system_d J L A p T R) (he : Fn0_d A Y e)
    (range : ∀ y, M.mem y Y ↔ ∃ a, Rd_entry_d a y e)
    (step : ∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
      (Rd_entry_d a b T ↔ Rd_entry_d i j L ∧ x = y))
    (rel : ∀ a b i j x y, Rd_entry_d a i p → Rd_entry_d b j p → Rd_entry_d a x e → Rd_entry_d b y e →
      (Rd_entry_d a b R ↔ i = j ∧ Rd_entry_d x y V))
    (bound : ∀ x y, Rd_entry_d x y V → M.mem x Y ∧ M.mem y Y)
    (graph : ∀ r, M.mem r V → ∃ x y, KPair_d M r x y) : Di_limit_d A p T R e Y V := by
  have val a b x y (hab : Rd_entry_d a b T) (hax : Rd_entry_d a x e) (hby : Rd_entry_d b y e) : x = y := by
    obtain ⟨i, _, hai⟩ := h.index.2.1 a (h.bound a b hab).1
    obtain ⟨j, _, hbj⟩ := h.index.2.1 b (h.bound a b hab).2
    exact ((step a b i j x y hai hbj hax hby).mp hab).2
  refine ⟨he, range, fun a b x y hax hby => ?_, fun a b x y hax hby => ?_, bound, graph⟩
  · constructor
    · intro eq
      obtain ⟨i, u, v, hui, hvi, hau, hbv⟩ := h.common_l (he.bound_l hax).1 (he.bound_l hby).1
      obtain ⟨z, _, huz⟩ := he.2.1 u (h.bound a u hau).2
      obtain ⟨w, _, hvw⟩ := he.2.1 v (h.bound b v hbv).2
      have same := (val a u x z hau hax huz).symm.trans (eq.trans (val b v y w hbv hby hvw))
      have huv := (step u v i i z w hui hvi huz hvw).mpr ⟨h.order.refl i (h.index.bound_l hui).2, same⟩
      have uv := h.unique u u v i hui hvi (h.identity u (h.bound a u hau).2) huv
      exact ⟨u, hau, uv.symm ▸ hbv⟩
    · rintro ⟨u, hau, hbu⟩
      obtain ⟨z, _, huz⟩ := he.2.1 u (h.bound a u hau).2
      exact (val a u x z hau hax huz).trans (val b u y z hbu hby huz).symm
  · constructor
    · intro hxy
      obtain ⟨i, u, v, hui, hvi, hau, hbv⟩ := h.common_l (he.bound_l hax).1 (he.bound_l hby).1
      obtain ⟨z, _, huz⟩ := he.2.1 u (h.bound a u hau).2
      obtain ⟨w, _, hvw⟩ := he.2.1 v (h.bound b v hbv).2
      exact ⟨i, u, v, hui, hvi, hau, hbv, (rel u v i i z w hui hvi huz hvw).mpr
        ⟨rfl, val a u x z hau hax huz ▸ val b v y w hbv hby hvw ▸ hxy⟩⟩
    · rintro ⟨i, u, v, hui, hvi, hau, hbv, huv⟩
      obtain ⟨z, _, huz⟩ := he.2.1 u (h.bound a u hau).2
      obtain ⟨w, _, hvw⟩ := he.2.1 v (h.bound b v hbv).2
      exact (val a u x z hau hax huz).symm ▸ (val b v y w hbv hby hvw).symm ▸
        ((rel u v i i z w hui hvi huz hvw).mp huv).2

end YesMetaZFC.SetTheory.Internal

/-! ## 任意定向子结构族的实际系统与良基极限

对给定实际集合族 `J`，构造带标号并集 `(i,x)`、全部包含映射和直接极限。
取值映射的像恰为各分量之并；此无限族实例只要求有限定向性，良基性只用 ZF。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_union_l (hZF : M.Models ZF) {J X V : M.Domain}
    (hb : ∀ i, M.mem i J → M.MemberSubset i X)
    (hd : ∀ i j, M.mem i J → M.mem j J → ∃ k, M.mem k J ∧ M.MemberSubset i k ∧ M.MemberSubset j k)
    (hw : Wf_rel_d X V) : ∃ L A p T R q C S g,
      Di_system_d J L A p T R ∧ Di_wf_d A p R ∧ Di_limit_d A p T R q C S ∧ Wf_rel_d C S ∧ Fn0_d C X g ∧
      (∀ i j, Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ M.MemberSubset i j) ∧
      (∀ a, M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x) ∧
      ∀ x, (∃ B, Rd_entry_d B x g) ↔ ∃ i, M.mem i J ∧ M.mem x i := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 0 := { body := Formula.subset (.bound 1) .newest }
  obtain ⟨L, _, hl⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ⟨Fin.elim0, fun _ => X⟩ J
  have ls i j : Rd_entry_d i j L ↔ M.mem i J ∧ M.mem j J ∧ M.MemberSubset i j :=
    (hl i j).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_subset_iff _ _ _)
  have ho : Di_order_d J L := ⟨fun i hi => (ls i i).mpr ⟨hi, hi, fun _ => id⟩,
    fun i j k hij hjk => (ls i k).mpr ⟨((ls i j).mp hij).1, ((ls j k).mp hjk).2.1,
      fun x hx => ((ls j k).mp hjk).2.2 x (((ls i j).mp hij).2.2 x hx)⟩,
    fun i j hij => ⟨((ls i j).mp hij).1, ((ls i j).mp hij).2.1⟩, fun i j hi hj => by
      obtain ⟨k, hk, hik, hjk⟩ := hd i j hi hj
      exact ⟨k, hk, (ls i k).mpr ⟨hi, hk, hik⟩, (ls j k).mpr ⟨hj, hk, hjk⟩⟩⟩
  obtain ⟨D, hD⟩ := ZF.exists_cartesianProduct hZF I J X
  let ψ : UnarySchema 1 := { body := Formula.existsMem (.bound 1) (Formula.existsMem .newest
    (kpair_m (.bound 2) (.bound 1) .newest)) }
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF ψ ⟨fun _ => J, fun _ => X⟩ D
  have aspec a : M.mem a A ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x := by
    have sat : ψ.denote ⟨fun _ => J, fun _ => X⟩ a ↔ ∃ i, M.mem i J ∧ ∃ x, M.mem x i ∧ KPair_d M a i x := by
      simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair_sat_l M hZF.1]; rfl
    exact (ha a).trans ((and_congr_right fun _ => sat).trans ⟨And.right,
      fun ⟨i, hi, x, hx, hp⟩ => ⟨(hD a).mpr ⟨i, hi, x, hb i hi x hx, hp⟩, i, hi, x, hx, hp⟩⟩)
  let first : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) (.bound 1) .newest) }
  let second : BinarySchema 0 := { body := .existsE (kpair_m (.bound 2) .newest (.bound 1)) }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  have fval a i : first.denote ρ a i ↔ ∃ x, KPair_d M a i x := by
    simp only [first, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  have sval a x : second.denote ρ a x ↔ ∃ i, KPair_d M a i x := by
    simp only [second, BinarySchema.denote, Formula.satisfies_exists_iff, kpair_sat_l M hZF.1]; rfl
  obtain ⟨p, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I first ρ (source := A) (target := J)
    (fun a ha => by
      obtain ⟨i, _, x, _, hax⟩ := (aspec a).mp ha
      exact ⟨i, (fval a i).mpr ⟨x, hax⟩⟩)
    (fun a _ i j hi hj => by
      obtain ⟨x, hx⟩ := (fval a i).mp hi
      obtain ⟨y, hy⟩ := (fval a j).mp hj
      exact (kpair_injective_l M hx hy).1)
    (fun a i ha hi => by
      obtain ⟨j, hj, x, _, hax⟩ := (aspec a).mp ha
      obtain ⟨y, hay⟩ := (fval a i).mp hi
      exact (kpair_injective_l M hax hay).1 ▸ hj)
  obtain ⟨e, he, es⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I second ρ (source := A) (target := X)
    (fun a ha => by
      obtain ⟨i, _, x, _, hax⟩ := (aspec a).mp ha
      exact ⟨x, (sval a x).mpr ⟨i, hax⟩⟩)
    (fun a _ x y hx hy => by
      obtain ⟨i, hi⟩ := (sval a x).mp hx
      obtain ⟨j, hj⟩ := (sval a y).mp hy
      exact (kpair_injective_l M hi hj).2)
    (fun a x ha hx => by
      obtain ⟨i, hi, y, hy, hay⟩ := (aspec a).mp ha
      obtain ⟨j, hax⟩ := (sval a x).mp hx
      exact (kpair_injective_l M hay hax).2 ▸ hb i hi y hy)
  have read a i x (hai : Rd_entry_d a i p) (hax : Rd_entry_d a x e) : KPair_d M a i x := by
    obtain ⟨y, hay⟩ := (fval a i).mp ((ps a i).mp hai).2
    obtain ⟨j, haj⟩ := (sval a x).mp ((es a x).mp hax).2
    exact (kpair_injective_l M hay haj).2 ▸ hay
  have node i x (hi : M.mem i J) (hx : M.mem x i) : ∃ a, Rd_entry_d a i p ∧ Rd_entry_d a x e := by
    obtain ⟨a, hax⟩ := I.total i x
    have ha := (aspec a).mpr ⟨i, hi, x, hx, hax⟩
    exact ⟨a, (ps a i).mpr ⟨ha, (fval a i).mpr ⟨x, hax⟩⟩, (es a x).mpr ⟨ha, (sval a x).mpr ⟨i, hax⟩⟩⟩
  have value a i x (hai : Rd_entry_d a i p) (hax : Rd_entry_d a x e) : M.mem x i := by
    obtain ⟨j, _, y, hy, hay⟩ := (aspec a).mp (hp.input_mem_of_pairMember hai)
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M hay (read a i x hai hax)
    exact hy
  obtain ⟨T, R, h, ts, rs⟩ := di_cone_system_l (V := V) hZF ho
    (fn0_of_function_l (ZF.modelsKP hZF) hp) (fn0_of_function_l (ZF.modelsKP hZF) he)
    (fun a b i x ha hb hax hbx => kpair_unique_l M hZF.1 (read a i x ha hax) (read b i x hb hbx))
    (fun a i j x hai hij hax => node j x ((ls i j).mp hij).2.1 (((ls i j).mp hij).2.2 x (value a i x hai hax)))
  obtain ⟨q, C, S, hq⟩ := di_limit_exists_l hZF h
  obtain ⟨g, hg, law, wf⟩ := di_cone_wf_l hZF h hq (fn0_of_function_l (ZF.modelsKP hZF) he) hw
    (fun a b x y hab hax hby => by
      obtain ⟨i, _, hai⟩ := hp.2.2 a (he.input_mem_of_pairMember hax)
      obtain ⟨j, _, hbj⟩ := hp.2.2 b (he.input_mem_of_pairMember hby)
      exact ((ts a b i j x y hai hbj hax hby).mp hab).2)
    (fun a b i x y hai hbi hax hby hab => ((rs a b i i x y hai hbi hax hby).mp hab).2)
  have wa : Wf_rel_d A R := wf_of_map_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) he) (by
    intro a b x y hab hax hby
    obtain ⟨i, hai, hbi⟩ := h.locality a b hab
    exact ((rs a b i i x y hai hbi hax hby).mp hab).2)
  refine ⟨L, A, p, T, R, q, C, S, g, h, fun _ B hB _ hn => wa B hB hn,
    hq, wf, hg, ls, aspec, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨B, hBx⟩
    obtain ⟨a, haB⟩ := (hq.range B).mp (hg.bound_l hBx).1
    obtain ⟨i, hi, hai⟩ := hp.2.2 a (hq.projection.bound_l haB).1
    obtain ⟨y, _, hay⟩ := he.2.2 a (hq.projection.bound_l haB).1
    have eq := (fn0_function_l (ZF.modelsKP hZF) hg).1.2 B y x (law a B y haB hay) hBx
    exact ⟨i, hi, eq ▸ value a i y hai hay⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨a, hai, hax⟩ := node i x hi hx
    obtain ⟨B, _, haB⟩ := hq.projection.2.1 a (hp.input_mem_of_pairMember hai)
    exact ⟨B, law a B x haB hax⟩

/-- 全部内部子集组成的系统是可数定向判据的实际实例，无需另给分量或映射。 -/
theorem di_power_limit_l (hZF : M.Models ZF) (ω X : M.Domain) :
    ∃ J L A p T R q C S, M.IsPowerSetOf J X ∧ Di_system_d J L A p T R ∧
      Di_sigma_d ω J L ∧ Di_wf_d A p R ∧ Di_limit_d A p T R q C S ∧ Wf_rel_d C S := by
  obtain ⟨J, hJ⟩ := ZF.exists_powerSet hZF X
  obtain ⟨V, hw, _⟩ := wf_membership_l hZF X
  have hx := (hJ X).mpr (fun _ => id)
  obtain ⟨L, A, p, T, R, q, C, S, _, hs, hwA, hq, hwC, _, hl, _⟩ := di_union_l hZF
    (fun i hi => (hJ i).mp hi)
    (fun i j hi hj => ⟨X, hx, (hJ i).mp hi, (hJ j).mp hj⟩) hw
  exact ⟨J, L, A, p, T, R, q, C, S, hJ, hs,
    di_sigma_of_top_l hx (fun i hi => (hl i X).mpr ⟨hi, hx, (hJ i).mp hi⟩), hwA, hq, hwC⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 定向系统分量的实际结构码

分量是标签图的纤维，关系是原分量关系的限制。非空纤维的载体、关系与
结构码均由分离构造；规范投影就是全系统商图在该纤维上的限制。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_stage_d (I : kpair_convention_l.Interpretation M) (A p R i c X S : M.Domain) : Prop :=
  Smdl_d I c X S ∧ (∀ x, M.mem x X ↔ M.mem x A ∧ Rd_entry_d x i p) ∧
  ∀ x y, Rd_entry_d x y S ↔ M.mem x X ∧ M.mem y X ∧ Rd_entry_d x y R

def di_stage_m {d} (A p R i c X S : Term d) : Formula 1 d :=
  .conj (smdl_m (𝒞 := kpair_convention_l) c X S) (.conj
    (.forallE (.iff (.mem .newest X.weaken) (.conj (.mem .newest A.weaken) (rd_entry_m .newest i.weaken p.weaken))))
    (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest S.weaken.weaken)
      (.conj (.mem (.bound 1) X.weaken.weaken) (.conj (.mem .newest X.weaken.weaken)
        (rd_entry_m (.bound 1) .newest R.weaken.weaken)))))))
derive_free_closed di_stage_m
theorem di_stage_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d}
    (ρ : Env M d) (A p R i c X S : Term d) : Formula.satisfies ρ (di_stage_m A p R i c X S) ↔
      Di_stage_d I (A.eval ρ) (p.eval ρ) (R.eval ρ) (i.eval ρ) (c.eval ρ) (X.eval ρ) (S.eval ρ) := by
  simp only [di_stage_m, Di_stage_d, Formula.satisfies_conj_iff, smdl_sat_l I,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem di_stage_exists_l (hZF : M.Models ZF) {J L A p T R i x : M.Domain}
    (h : Di_system_d J L A p T R) (hx : Rd_entry_d x i p) :
    ∃ c X S, Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : UnarySchema 2 := { body := rd_entry_m .newest (.bound 1) (.bound 2) }
  obtain ⟨X, hs⟩ := ZF.separation_exists_d hZF φ ⟨Fin.cases i (fun _ => p), fun _ => A⟩ A
  have spec y : M.mem y X ↔ M.mem y A ∧ Rd_entry_d y i p :=
    (hs y).trans (and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)
  let ψ : BinarySchema 1 := { body := rd_entry_m (.bound 1) .newest (.bound 2) }
  obtain ⟨S, hr, read⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ⟨fun _ => R, fun _ => R⟩ X
  obtain ⟨c, hc⟩ := I.total X S
  exact ⟨c, X, S, ⟨hc, ⟨x, (spec x).mpr ⟨(h.index.bound_l hx).1, hx⟩⟩, hr⟩, spec,
    fun x y => (read x y).trans (and_congr_right fun _ => and_congr_right fun _ => rd_entry_sat_l hZF.1 _ _ _ _)⟩

/-- 全初等的过渡图；每张图都精确等于原系统在两分量之间的过渡。 -/
def Di_elementary_d (I : kpair_convention_l.Interpretation M) (ω L A p T R : M.Domain) : Prop :=
  ∀ i j c X S d Y V, Di_stage_d I A p R i c X S → Di_stage_d I A p R j d Y V → Rd_entry_d i j L →
    ∃ e, Smap_d I ω c d X Y e ∧ ∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ M.mem y Y ∧ Rd_entry_d x y T

theorem di_projection_l (hZF : M.Models ZF) {J L A p T R q C V i c X S : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S) :
    ∃ e, M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) e X C ∧
      (∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ Rd_entry_d x y q) ∧
      ∀ x y u v, Rd_entry_d x u e → Rd_entry_d y v e → (Rd_entry_d x y S ↔ Rd_entry_d u v V) := by
  obtain ⟨Y, e, hy, he, spec, inj, rel⟩ := di_stage_l hZF h limit i
  have eq := hZF.1.eq_of_same_members Y X (fun x => (hy x).trans (stage.2.1 x).symm)
  subst Y
  refine ⟨e, ⟨fn0_function_l (ZF.modelsKP hZF) he, inj⟩, spec, fun x y u v hx hy => ?_⟩
  have read : (M.mem x X ∧ M.mem y X ∧ Rd_entry_d x y R) ↔ Rd_entry_d x y R :=
    ⟨And.right ∘ And.right, fun hr => ⟨(he.bound_l hx).1, (he.bound_l hy).1, hr⟩⟩
  exact (stage.2.2 x y).trans (read.trans (rel x y u v hx hy).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 同时量化全部分量的内部初等性归纳公式 -/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Di_row_d (I : kpair_convention_l.Interpretation M) (ω A p R C V K F n q r : M.Domain) : Prop :=
  ∀ i c X S E, Di_stage_d I A p R i c X S → M.IsFunctionSpace I E ω X →
    Smap_row_d I ω X S E C V K F n q r

def di_row_m {d} (ω A p R C V K F n q r : Term d) : Formula 1 d :=
  let w (x : Term d) : Term (d+5) := x.weaken.weaken.weaken.weaken.weaken
  .forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (di_stage_m (w A) (w p) (w R) (.bound 4) (.bound 3) (.bound 2) (.bound 1))
    (.imp (Formula.isFunctionSpace kpair_convention_l .newest (w ω) (.bound 2))
      (smap_row_m (𝒞 := kpair_convention_l) (w ω) (.bound 2) (.bound 1) .newest
        (w C) (w V) (w K) (w F) (w n) (w q) (w r))))))))
@[simp] theorem di_row_closed_l {d} (ω A p R C V K F n q r : Term d)
    (hω : ω.freeSupport = []) (hA : A.freeSupport = []) (hp : p.freeSupport = []) (hR : R.freeSupport = [])
    (hC : C.freeSupport = []) (hV : V.freeSupport = []) (hK : K.freeSupport = []) (hF : F.freeSupport = [])
    (hn : n.freeSupport = []) (hq : q.freeSupport = []) (hr : r.freeSupport = []) :
    (di_row_m ω A p R C V K F n q r).FreeClosed := by
  simp -implicitDefEqProofs [di_row_m, Formula.isFunctionSpace, Definitional.Formula.FreeClosed,
    hω, hA, hp, hR, hC, hV, hK, hF, hn, hq, hr]
theorem di_row_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d} (ρ : Env M d)
    (ω A p R C V K F n q r : Term d) : Formula.satisfies ρ (di_row_m ω A p R C V K F n q r) ↔
      Di_row_d I (ω.eval ρ) (A.eval ρ) (p.eval ρ) (R.eval ρ) (C.eval ρ) (V.eval ρ) (K.eval ρ)
        (F.eval ρ) (n.eval ρ) (q.eval ρ) (r.eval ρ) := by
  simp only [di_row_m, Di_row_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    di_stage_sat_l I hE, Formula.satisfies_isFunctionSpace_iff I hE, smap_row_sat_l I hE,
    Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 初等定向系统的极限保持全部内部公式码

在同时量化所有分量的原公式上归纳。存在量词反向时，把当前分量和目标
见证移到共同后继；该步只用有限定向性，不要求整张 ω 赋值有共同上界。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_row_l (hZF : M.Models ZF) {ω J L A p T R q C V K F n r : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p T R)
    (hK : M.IsFunctionSpace (kp_pair_l (ZF.modelsKP hZF)) K ω C)
    (hF : Sfm_d (kp_pair_l (ZF.modelsKP hZF)) ω n F) (hr : M.mem r n) :
    Di_row_d (kp_pair_l (ZF.modelsKP hZF)) ω A p R C V K F n q r := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have hq := fn0_function_l (ZF.modelsKP hZF) limit.projection
  obtain ⟨H, hH⟩ := seval_exists_l I hZF C V K F hF.2.1.1
  let ρ := (((((((((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push p).push R).push C).push V).push K).push F).push n).push q
  let φ : UnarySchema 10 := {
    body := di_row_m (.bound 10) (.bound 9) (.bound 8) (.bound 7)
      (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have sat t : φ.denote ρ t ↔ Di_row_d I ω A p R C V K F n q t := di_row_sat_l I hZF.1 ..
  apply (sat r).mp (sfm_induction_l I hZF hF φ ρ ?_ hr)
  intro r hr ih
  apply (sat r).mpr
  intro i c X S E stage hE f g hf hg hfg
  obtain ⟨D, hD⟩ := seval_exists_l I hZF X S E F hF.2.1.1
  have ff := (hE f).mp hf
  have point k (hk : M.mem k ω) : ∃ x y, M.PairMember I k x f ∧ M.PairMember I x y q ∧ M.PairMember I k y g := by
    obtain ⟨x, hx, hkx⟩ := ff.2.2 k hk
    obtain ⟨y, _, hxy⟩ := hq.2.2 x (((stage.2.1 x).mp hx).1)
    exact ⟨x, y, hkx, hxy, hfg k hk x y hkx hxy⟩
  have label x k (hkx : M.PairMember I k x f) := ((stage.2.1 x).mp (ff.output_mem_of_pairMember hkx)).2
  obtain ⟨o, ho⟩ := (hF.2.1.2.2 r).mp hr
  rcases hF.2.2 r o ho with ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩ |
    ⟨a, b, hs, ha, hb⟩ | ⟨a, b, hs, ha, hb⟩
  · obtain ⟨x, u, hax, hxu, hau⟩ := point a ha
    obtain ⟨y, v, hby, hyv, hbv⟩ := point b hb
    have rel : Rd_entry_d x y S ↔ Rd_entry_d u v V := by
      have read : Rd_entry_d x y S ↔ Rd_entry_d x y R := (stage.2.2 x y).trans
        ⟨And.right ∘ And.right, fun hr => ⟨ff.output_mem_of_pairMember hax, ff.output_mem_of_pairMember hby, hr⟩⟩
      exact read.trans ((h.rel_at_l (label x a hax) (label y b hby)
        (h.identity x (h.index.bound_l (label x a hax)).1) (h.identity y (h.index.bound_l (label y b hby)).1)).symm.trans
          (limit.relation x y u v hxu hyv).symm)
    exact (ssat_rel_l I hZF hF hD ho hs hE hf hax hby).trans
      (rel.trans (ssat_rel_l I hZF hF hH ho hs hK hg hau hbv).symm)
  · obtain ⟨x, u, hax, hxu, hau⟩ := point a ha
    obtain ⟨y, v, hby, hyv, hbv⟩ := point b hb
    have eq := ((limit.kernel x y u v hxu hyv).trans (h.eq_at_l (label x a hax) (label y b hby))).symm
    exact (ssat_eq_l I hZF hF hD ho hs hE hf hax hby).trans
      (eq.trans (ssat_eq_l I hZF hF hH ho hs hK hg hau hbv).symm)
  · exact (ssat_nor_l I hZF hF hD ho hs hf).trans ((not_congr (or_congr
      ((sat a).mp (ih a ha) i c X S E stage hE f g hf hg hfg)
      ((sat b).mp (ih b hb) i c X S E stage hE f g hf hg hfg))).trans (ssat_nor_l I hZF hF hH ho hs hg).symm)
  · rw [ssat_exists_l I hZF hF hD ho hs hf, ssat_exists_l I hZF hF hH ho hs hg]
    constructor
    · rintro ⟨x, f', hx, hu, truth⟩
      obtain ⟨y, hy, hxy⟩ := hq.2.2 x (((stage.2.1 x).mp hx).1)
      obtain ⟨g', hv, hgv⟩ := senv_update_exists_l I hZF ((hK g).mp hg) ha hy
      exact ⟨y, g', hy, hv, ((sat b).mp (ih b hb) i c X S E stage hE f' g'
        ((hE f').mpr (hu.function_l I ff ha hx)) ((hK g').mpr hgv)
        (hfg.update_l I hq.1 hxy hu hv)).mp truth⟩
    · rintro ⟨y, g', hy, hv, truth⟩
      -- 新见证在某一分量有代表；共同后继同时容纳它和原赋值的整个分量。
      obtain ⟨v, hvy⟩ := (limit.range y).mp hy
      obtain ⟨j, hj, hvj⟩ := h.index.2.1 v (limit.projection.bound_l hvy).1
      obtain ⟨x, hx⟩ := stage.1.2.1
      have hxi := ((stage.2.1 x).mp hx).2
      obtain ⟨k, _, hik, hjk⟩ := h.order.directed i j (h.index.bound_l hxi).2 hj
      obtain ⟨w, hwk, hvw⟩ := h.total v j k hvj hjk
      obtain ⟨d, Y, W, next⟩ := di_stage_exists_l hZF h hwk
      obtain ⟨e, he, es⟩ := elementary i k c X S d Y W stage next hik
      obtain ⟨f₁, hf₁, assign⟩ := smap_assign_exists_l I hZF he.1.1 ff
      obtain ⟨E₁, hE₁⟩ := ZF.exists_functionSpace hZF I ω Y
      obtain ⟨H₁, hH₁⟩ := seval_exists_l I hZF Y W E₁ F hF.2.1.1
      have hwy : Rd_entry_d w y q := by
        obtain ⟨z, _, hwz⟩ := limit.projection.2.1 w (h.bound v w hvw).2
        exact (limit.commute_l h hvw hvy hwz).symm ▸ hwz
      have projected : Smap_assign_d I ω q f₁ g := by
        intro t ht u z htu huz
        obtain ⟨x, hx, htx⟩ := ff.2.2 t ht
        obtain ⟨u', _, hxu⟩ := he.1.1.2.2 x hx
        have eq := hf₁.1.2 t u' u (assign t ht x u' htx hxu) htu
        subst u'
        obtain ⟨z', _, hxz⟩ := limit.projection.2.1 x (((stage.2.1 x).mp hx).1)
        have eq := limit.commute_l h (((es x u).mp hxu).2.2) hxz huz
        exact hfg t ht x z htx (eq ▸ hxz)
      have hwY := (next.2.1 w).mpr ⟨(h.index.bound_l hwk).1, hwk⟩
      obtain ⟨f₂, update, hf₂⟩ := senv_update_exists_l I hZF hf₁ ha hwY
      have body := ((sat b).mp (ih b hb) k d Y W E₁ next hE₁ f₂ g' ((hE₁ f₂).mpr hf₂)
        ((hK g').mpr (hv.function_l I ((hK g).mp hg) ha hy)) (projected.update_l I hq.1 hwy update hv)).mpr truth
      have future := (ssat_exists_l I hZF hF hH₁ ho hs ((hE₁ f₁).mpr hf₁)).mpr ⟨w, f₂, hwY, update, body⟩
      exact (ssat_exists_l I hZF hF hD ho hs hf).mp
        ((he.ssat_l I hZF.1 stage.1 next.1 hF hr hE hE₁ hf ((hE₁ f₁).mpr hf₁) assign).mpr future)

/-- 每个分量的规范投影都是完整内部初等嵌入。 -/
theorem di_elementary_limit_l (hZF : M.Models ZF) {ω J L A p T R q C V i c X S d : M.Domain}
    (hω : M.IsOmega ω) (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (elementary : Di_elementary_d (kp_pair_l (ZF.modelsKP hZF)) ω L A p T R)
    (stage : Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S)
    (model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d C V) :
    ∃ e, Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X C e ∧
      ∀ x y, Rd_entry_d x y e ↔ M.mem x X ∧ Rd_entry_d x y q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨e, he, spec, _⟩ := di_projection_l hZF h limit stage
  obtain ⟨Z, hZ⟩ := scode_exists_l I hZF hω
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω C
  refine ⟨e, ⟨he, Z, hZ, fun a f g ha hf hg hfg => ?_⟩, spec⟩
  obtain ⟨n, F, r, hc⟩ := (hZ a).mp ha
  have assign : Smap_assign_d I ω q f g := fun i hi x y hx hy => hfg i hi x y hx
    ((spec x y).mpr ⟨hf.output_mem_of_pairMember hx, hy⟩)
  exact (satisfies_decode_l I hZF.1 stage.1 hc hE).trans
    ((di_row_l hZF h limit elementary hK hc.2.1 hc.2.2 i c X S E stage hE f g ((hE f).mpr hf) ((hK g).mpr hg) assign).trans
      (satisfies_decode_l I hZF.1 model hc hK).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 任意内部有限赋值可以放入共同分量

在原公式上归纳，把有限多个类推到共同分量。该分量上的投影为单射，
所以代表随后由唯一值收集构造；全程只需 ZF，不选择可数代表族。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem di_finite_cover_l (hZF : M.Models ZF) {ω J L A p T R q C V b f : M.Domain}
    (hω : M.IsOmega ω) (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V)
    (hb : M.mem b ω) (hf : Fn0_d ω C f) : ∃ i c X S a,
      Di_stage_d (kp_pair_l (ZF.modelsKP hZF)) A p R i c X S ∧ Fn0_d ω X a ∧
      ∀ j x B, M.mem j b → Rd_entry_d j x a → Rd_entry_d j B f → Rd_entry_d x B q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have push {x i j B} (hxi : Rd_entry_d x i p) (hij : Rd_entry_d i j L) (hxB : Rd_entry_d x B q) :
      ∃ y, Rd_entry_d y j p ∧ Rd_entry_d y B q := by
    obtain ⟨y, hyj, hxy⟩ := h.total x i j hxi hij
    obtain ⟨E, _, hyE⟩ := limit.projection.2.1 y (h.bound x y hxy).2
    exact ⟨y, hyj, (limit.commute_l h hxy hxB hyE).symm ▸ hyE⟩
  obtain ⟨z, _, hzω⟩ := hω.1.1
  obtain ⟨B₀, hB₀, _⟩ := hf.2.1 z hzω
  obtain ⟨x₀, hx₀⟩ := (limit.range B₀).mp hB₀
  obtain ⟨i₀, hi₀, hx₀i⟩ := h.index.2.1 x₀ (limit.projection.bound_l hx₀).1
  let ρ : Env M 6 := ⟨Fin.cases J (Fin.cases p (Fin.cases q (Fin.cases f (Fin.cases L (fun _ => i₀))))), fun _ => f⟩
  let φ : UnarySchema 6 := {
    body := Formula.existsMem (.bound 1) (.conj (rd_entry_m (.bound 7) .newest (.bound 6)) (Formula.forallMem (.bound 1)
      (.forallE (.imp (rd_entry_m (.bound 1) .newest (.bound 7)) (.existsE
        (.conj (rd_entry_m .newest (.bound 3) (.bound 6)) (rd_entry_m .newest (.bound 1) (.bound 7)))))))) }
  have sat n : φ.denote ρ n ↔ ∃ i, M.mem i J ∧ Rd_entry_d i₀ i L ∧
      ∀ j, M.mem j n → ∀ B, Rd_entry_d j B f → ∃ x, Rd_entry_d x i p ∧ Rd_entry_d x B q := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1]; rfl
  have all : ∀ n, M.mem n ω → φ.denote ρ n := by
    apply hω.induction (fun n => φ.denote ρ n) (ZF.separation_exists_d hZF φ ρ ω)
    · exact fun e he => (sat e).mpr ⟨i₀, hi₀, h.order.refl i₀ hi₀, fun j hj => (he j hj).elim⟩
    · intro n hn ih m hs
      obtain ⟨i, hi, h₀i, bound⟩ := (sat n).mp ih
      obtain ⟨B, hB, hnB⟩ := hf.2.1 n hn
      obtain ⟨x, hxB⟩ := (limit.range B).mp hB
      obtain ⟨j, hj, hxj⟩ := h.index.2.1 x (limit.projection.bound_l hxB).1
      obtain ⟨k, hk, hik, hjk⟩ := h.order.directed i j hi hj
      refine (sat m).mpr ⟨k, hk, h.order.trans i₀ i k h₀i hik, fun a ha E haE => ?_⟩
      rcases (hs a).mp ha with ha | ha
      · obtain ⟨y, hyi, hyE⟩ := bound a ha E haE
        exact push hyi hik hyE
      · have ea := hZF.1.eq_of_same_members a n ha
        have eB := hf.2.2 n hn B hB E (hf.bound_l haE).2 hnB (ea ▸ haE)
        exact eB ▸ push hxj hjk hxB
  obtain ⟨i, _, h₀i, bound⟩ := (sat b).mp (all b hb)
  obtain ⟨w, hwi, _⟩ := push hx₀i h₀i hx₀
  obtain ⟨c, X, S, stage⟩ := di_stage_exists_l hZF h hwi
  have hwX := (stage.2.1 w).mpr ⟨(h.index.bound_l hwi).1, hwi⟩
  let η : Env M 5 := ⟨Fin.cases X (Fin.cases b (Fin.cases f (Fin.cases q (fun _ => w)))), fun _ => f⟩
  let ψ : BinarySchema 5 := {
    body := .conj (.mem .newest (.bound 2)) (.disj (.conj (.mem (.bound 1) (.bound 3)) (.existsE
      (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m (.bound 1) .newest (.bound 6)))))
      (.conj (.neg (.mem (.bound 1) (.bound 3))) (Formula.extensionalEq .newest (.bound 6)))) }
  have read j y : ψ.denote η j y ↔ M.mem y X ∧
      ((M.mem j b ∧ ∃ B, Rd_entry_d j B f ∧ Rd_entry_d y B q) ∨ (¬ M.mem j b ∧ y = w)) := by
    simp only [ψ, BinarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_disj_iff, Formula.satisfies_exists_iff, rd_entry_sat_l hZF.1,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
  have total j (hj : M.mem j ω) : ∃ y, ψ.denote η j y := by
    classical
    by_cases hjb : M.mem j b
    · obtain ⟨B, _, hjB⟩ := hf.2.1 j hj
      obtain ⟨x, hxi, hxB⟩ := bound j hjb B hjB
      exact ⟨x, (read j x).mpr ⟨(stage.2.1 x).mpr ⟨(h.index.bound_l hxi).1, hxi⟩, Or.inl ⟨hjb, B, hjB, hxB⟩⟩⟩
    · exact ⟨w, (read j w).mpr ⟨hwX, Or.inr ⟨hjb, rfl⟩⟩⟩
  have unique j (hj : M.mem j ω) x y (hx : ψ.denote η j x) (hy : ψ.denote η j y) : x = y := by
    obtain ⟨hxX, hx⟩ := (read j x).mp hx
    obtain ⟨hyX, hy⟩ := (read j y).mp hy
    rcases hx with ⟨hb, B, hjB, hxB⟩ | ⟨hb, rfl⟩ <;>
      rcases hy with ⟨hb', E, hjE, hyE⟩ | ⟨hb', rfl⟩
    · exact (h.eq_at_l ((stage.2.1 x).mp hxX).2 ((stage.2.1 y).mp hyX).2).mp
        ((limit.kernel x y B E hxB hyE).mp (hf.2.2 j hj B (hf.bound_l hjB).2 E (hf.bound_l hjE).2 hjB hjE))
    · exact (hb' hb).elim
    · exact (hb hb').elim
    · rfl
  obtain ⟨a, ha, select⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I ψ η total unique
    (fun j y _ hy => ((read j y).mp hy).1)
  refine ⟨i, c, X, S, a, stage, fn0_of_function_l (ZF.modelsKP hZF) ha, fun j y B hj hy hjB => ?_⟩
  rcases ((read j y).mp ((select j y).mp hy).2).2 with ⟨_, E, hjE, hyE⟩ | ⟨hn, _⟩
  · exact hf.2.2 j (hω.transitive (ZF.modelsKP hZF) b hb j hj) E (hf.bound_l hjE).2 B (hf.bound_l hjB).2 hjE hjB ▸ hyE
  · exact (hn hj).elim

end YesMetaZFC.SetTheory.Internal

/-! ## 在同一直接极限上更换关系

关系沿实际商投影拉回各纤维，原来的载体、等价类和过渡图全部复用。
这使谓词扩张能够消费同一个直接极限，而无需重新构造一套商对象。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem smdl_pull_l {X Y f : M.Domain} (hX : ∃ x, M.mem x X)
    (hf : M.IsSetFunctionFromTo I f X Y) (R : M.Domain) : ∃ c S, Smdl_d I c X S ∧
      ∀ x y u v, Rd_entry_d x u f → Rd_entry_d y v f → (Rd_entry_d x y S ↔ Rd_entry_d u v R) := by
  let ρ := (⟨fun _ => f, fun _ => f⟩ : Env M 1).push R
  let φ : BinarySchema 2 := {
    body := .existsE (.existsE (.conj (rd_entry_m (.bound 3) (.bound 1) (.bound 5))
      (.conj (rd_entry_m (.bound 2) .newest (.bound 5)) (rd_entry_m (.bound 1) .newest (.bound 4))))) }
  have sat x y : φ.denote ρ x y ↔ ∃ u v, Rd_entry_d x u f ∧ Rd_entry_d y v f ∧ Rd_entry_d u v R := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨c, S, hm, spec⟩ := smdl_exists_l I hZF φ ρ hX
  refine ⟨c, S, hm, fun x y u v hx hy => ((spec x y).trans
    (and_congr_right fun _ => and_congr_right fun _ => sat x y)).trans ?_⟩
  exact ⟨fun ⟨_, _, a, b, ha, hb, hr⟩ => hf.1.2 x a u ha hx ▸ hf.1.2 y b v hb hy ▸ hr,
    fun hr => ⟨hf.input_mem_of_pairMember hx, hf.input_mem_of_pairMember hy, u, v, hx, hy, hr⟩⟩

theorem di_relation_change_l {J L A p T R q C V c W : M.Domain}
    (h : Di_system_d J L A p T R) (limit : Di_limit_d A p T R q C V) (hm : Smdl_d I c C W) :
    ∃ S, Di_system_d J L A p T S ∧ Di_limit_d A p T S q C W ∧
      ∀ x y i E H, Rd_entry_d x i p → Rd_entry_d y i p → Rd_entry_d x E q → Rd_entry_d y H q →
        (Rd_entry_d x y S ↔ Rd_entry_d E H W) := by
  let ρ := ((⟨fun _ => p, fun _ => p⟩ : Env M 1).push q).push W
  let φ : BinarySchema 3 := {
    body := .existsE (.existsE (.existsE (.conj (rd_entry_m (.bound 4) (.bound 2) (.bound 7))
      (.conj (rd_entry_m (.bound 3) (.bound 2) (.bound 7)) (.conj
        (rd_entry_m (.bound 4) (.bound 1) (.bound 6)) (.conj
          (rd_entry_m (.bound 3) .newest (.bound 6)) (rd_entry_m (.bound 1) .newest (.bound 5)))))))) }
  have sat x y : φ.denote ρ x y ↔ ∃ i E H, Rd_entry_d x i p ∧ Rd_entry_d y i p ∧
      Rd_entry_d x E q ∧ Rd_entry_d y H q ∧ Rd_entry_d E H W := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨S, _, spec⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ A
  have read x y i E H (hx : Rd_entry_d x i p) (hy : Rd_entry_d y i p)
      (he : Rd_entry_d x E q) (hh : Rd_entry_d y H q) : Rd_entry_d x y S ↔ Rd_entry_d E H W := by
    refine ((spec x y).trans (and_congr_right fun _ => and_congr_right fun _ => sat x y)).trans ⟨?_, ?_⟩
    · rintro ⟨_, _, _, E', H', _, _, he', hh', hr⟩
      exact (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 x E' E he' he ▸
        (fn0_function_l (ZF.modelsKP hZF) limit.projection).1.2 y H' H hh' hh ▸ hr
    · exact fun hr => ⟨(h.index.bound_l hx).1, (h.index.bound_l hy).1, i, E, H, hx, hy, he, hh, hr⟩
  have system : Di_system_d J L A p T S := { h with
    locality := fun x y hxy => by
      obtain ⟨_, _, ht⟩ := (spec x y).mp hxy
      obtain ⟨i, _, _, hx, hy, _⟩ := (sat x y).mp ht
      exact ⟨i, hx, hy⟩
    relation := fun x y i u v k hx hy hu hv hxu hyv => by
      obtain ⟨E, _, he⟩ := limit.projection.2.1 x (h.index.bound_l hx).1
      obtain ⟨H, _, hh⟩ := limit.projection.2.1 y (h.index.bound_l hy).1
      obtain ⟨E', _, he'⟩ := limit.projection.2.1 u (h.index.bound_l hu).1
      obtain ⟨H', _, hh'⟩ := limit.projection.2.1 v (h.index.bound_l hv).1
      have eqE := limit.commute_l h hxu he he'
      have eqH := limit.commute_l h hyv hh hh'
      subst E' H'
      exact (read x y i E H hx hy he hh).trans (read u v k E H hu hv he' hh').symm }
  refine ⟨S, system, ⟨limit.projection, limit.range, limit.kernel, ?_, ?_, hm.2.2.1⟩, read⟩
  · intro x y E H he hh
    obtain ⟨i, u, v, hu, hv, hxu, hyv⟩ := h.common_l (limit.projection.bound_l he).1 (limit.projection.bound_l hh).1
    obtain ⟨E', _, he'⟩ := limit.projection.2.1 u (h.index.bound_l hu).1
    obtain ⟨H', _, hh'⟩ := limit.projection.2.1 v (h.index.bound_l hv).1
    have eqE := limit.commute_l h hxu he he'
    have eqH := limit.commute_l h hyv hh hh'
    exact eqE ▸ eqH ▸ (read u v i E' H' hu hv he' hh').symm.trans (system.rel_at_l hu hv hxu hyv).symm
  · intro E H hEH
    exact hm.2.2.2 E H hEH

end YesMetaZFC.SetTheory.Internal

/-! ## 原定向系统及指定直接极限的传递读取

每个无界见证都出现在已有图条目中，故由图的拥有性回收。核与极限关系
因而仍是原共同后继关系，不把它们换成另一张等价关系。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
include hKP hZ
local notation "N" => rt_model_l Z nz

theorem rt_di_order_l (J L : (N).Domain) (h : Di_order_d J L) : Di_order_d J.val L.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨fun i hi => (ent ..).mp (h.refl ⟨i, hZ J.val J.property i hi⟩ hi), ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have ij := rd_entry_transitive_l hZ L.property hij
    have jk := rd_entry_transitive_l hZ L.property hjk
    exact (ent ..).mp (h.trans ⟨i, ij.1⟩ ⟨j, ij.2⟩ ⟨k, jk.2⟩ ((ent ..).mpr hij) ((ent ..).mpr hjk))
  · intro i j hij
    have ij := rd_entry_transitive_l hZ L.property hij
    exact h.bound ⟨i, ij.1⟩ ⟨j, ij.2⟩ ((ent ..).mpr hij)
  · intro i j hi hj
    obtain ⟨k, hk, hik, hjk⟩ := h.directed ⟨i, hZ J.val J.property i hi⟩ ⟨j, hZ J.val J.property j hj⟩ hi hj
    exact ⟨k.val, hk, (ent ..).mp hik, (ent ..).mp hjk⟩

theorem rt_di_system_l (J L A p T R : (N).Domain) (h : Di_system_d J L A p T R) :
    Di_system_d J.val L.val A.val p.val T.val R.val := by
  have ent := rt_entry_l hZ nz hKP.1
  have mem (f : (N).Domain) {x y} (h : Rd_entry_d x y f.val) := rd_entry_transitive_l hZ f.property h
  refine ⟨rt_di_order_l hKP hZ nz J L h.order, (rt_fn_l hZ nz hKP.1 ..).mp h.index,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact h.bound ⟨x, (mem T hxy).1⟩ ⟨y, (mem T hxy).2⟩ ((ent ..).mpr hxy)
  · intro x y i j hxi hyj hxy
    exact (ent ..).mp (h.forward ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyj).1⟩
      ⟨i, (mem p hxi).2⟩ ⟨j, (mem p hyj).2⟩ ((ent ..).mpr hxi) ((ent ..).mpr hyj) ((ent ..).mpr hxy))
  · intro x hx
    exact (ent ..).mp (h.identity ⟨x, hZ A.val A.property x hx⟩ hx)
  · intro x y z hxy hyz
    exact (ent ..).mp (h.comp ⟨x, (mem T hxy).1⟩ ⟨y, (mem T hxy).2⟩ ⟨z, (mem T hyz).2⟩
      ((ent ..).mpr hxy) ((ent ..).mpr hyz))
  · intro x i j hxi hij
    obtain ⟨y, hyj, hxy⟩ := h.total ⟨x, (mem p hxi).1⟩ ⟨i, (mem p hxi).2⟩ ⟨j, (mem L hij).2⟩
      ((ent ..).mpr hxi) ((ent ..).mpr hij)
    exact ⟨y.val, (ent ..).mp hyj, (ent ..).mp hxy⟩
  · intro x y z j hyj hzj hxy hxz
    exact congrArg Subtype.val (h.unique ⟨x, (mem T hxy).1⟩ ⟨y, (mem p hyj).1⟩ ⟨z, (mem p hzj).1⟩
      ⟨j, (mem p hyj).2⟩ ((ent ..).mpr hyj) ((ent ..).mpr hzj) ((ent ..).mpr hxy) ((ent ..).mpr hxz))
  · intro x y z i hxi hyi hxz hyz
    exact congrArg Subtype.val (h.injective ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyi).1⟩ ⟨z, (mem T hxz).2⟩
      ⟨i, (mem p hxi).2⟩ ((ent ..).mpr hxi) ((ent ..).mpr hyi) ((ent ..).mpr hxz) ((ent ..).mpr hyz))
  · intro x y hxy
    obtain ⟨i, hxi, hyi⟩ := h.locality ⟨x, (mem R hxy).1⟩ ⟨y, (mem R hxy).2⟩ ((ent ..).mpr hxy)
    exact ⟨i.val, (ent ..).mp hxi, (ent ..).mp hyi⟩
  · intro x y i u v j hxi hyi huj hvj hxu hyv
    exact (ent ⟨x, (mem p hxi).1⟩ ⟨y, (mem p hyi).1⟩ R).symm.trans
      ((h.relation _ _ ⟨i, (mem p hxi).2⟩ ⟨u, (mem p huj).1⟩ ⟨v, (mem p hvj).1⟩ ⟨j, (mem p huj).2⟩
        ((ent ..).mpr hxi) ((ent ..).mpr hyi) ((ent ..).mpr huj) ((ent ..).mpr hvj)
        ((ent ..).mpr hxu) ((ent ..).mpr hyv)).trans (ent ..))

theorem rt_di_eq_l (T x y : (N).Domain) : Di_eq_d T x y ↔ Di_eq_d T.val x.val y.val := by
  have ent := rt_entry_l hZ nz hKP.1
  exact ⟨fun ⟨z, hx, hy⟩ => ⟨z.val, (ent ..).mp hx, (ent ..).mp hy⟩,
    fun ⟨z, hx, hy⟩ => ⟨⟨z, (rd_entry_transitive_l hZ T.property hx).2⟩, (ent ..).mpr hx, (ent ..).mpr hy⟩⟩

theorem rt_di_rel_l (p T R x y : (N).Domain) :
    Di_rel_d p T R x y ↔ Di_rel_d p.val T.val R.val x.val y.val := by
  have ent := rt_entry_l hZ nz hKP.1
  constructor
  · rintro ⟨i, u, v, hui, hvi, hxu, hyv, huv⟩
    exact ⟨i.val, u.val, v.val, (ent ..).mp hui, (ent ..).mp hvi, (ent ..).mp hxu, (ent ..).mp hyv, (ent ..).mp huv⟩
  · rintro ⟨i, u, v, hui, hvi, hxu, hyv, huv⟩
    have ui := rd_entry_transitive_l hZ p.property hui
    have vi := rd_entry_transitive_l hZ p.property hvi
    exact ⟨⟨i, ui.2⟩, ⟨u, ui.1⟩, ⟨v, vi.1⟩,
      (ent ..).mpr hui, (ent ..).mpr hvi, (ent ..).mpr hxu, (ent ..).mpr hyv, (ent ..).mpr huv⟩

theorem rt_di_limit_l
    (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
    (A p T R q C S : (N).Domain) (h : Di_limit_d A p T R q C S) :
    Di_limit_d A.val p.val T.val R.val q.val C.val S.val := by
  have ent := rt_entry_l hZ nz hKP.1
  refine ⟨(rt_fn_l hZ nz hKP.1 ..).mp h.projection,
    (rt_range_l hZ nz hKP.1 (KP.exists_pair hKP) pair C q).mp h.range, ?_, ?_, ?_,
    (rt_relation_l hKP.1 (KP.exists_pair hKP) hZ nz pair S).mp h.graph⟩
  · intro x y B D hx hy
    have xb := rd_entry_transitive_l hZ q.property hx
    have yd := rd_entry_transitive_l hZ q.property hy
    exact (show B = D ↔ (⟨B, xb.2⟩ : (N).Domain) = ⟨D, yd.2⟩ from
      ⟨fun e => Subtype.ext e, congrArg Subtype.val⟩).trans
      ((h.kernel ⟨x, xb.1⟩ ⟨y, yd.1⟩ ⟨B, xb.2⟩ ⟨D, yd.2⟩ ((ent ..).mpr hx) ((ent ..).mpr hy)).trans
        (rt_di_eq_l hKP hZ nz ..))
  · intro x y B D hx hy
    have xb := rd_entry_transitive_l hZ q.property hx
    have yd := rd_entry_transitive_l hZ q.property hy
    exact (ent ⟨B, xb.2⟩ ⟨D, yd.2⟩ S).symm.trans
      ((h.relation ⟨x, xb.1⟩ ⟨y, yd.1⟩ ⟨B, xb.2⟩ ⟨D, yd.2⟩ ((ent ..).mpr hx) ((ent ..).mpr hy)).trans
        (rt_di_rel_l hKP hZ nz ..))
  · intro B D hBD
    have bd := rd_entry_transitive_l hZ S.property hBD
    exact h.bounded ⟨B, bd.1⟩ ⟨D, bd.2⟩ ((ent ..).mpr hBD)

end YesMetaZFC.SetTheory.Internal
