import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Basic
import YesMetaZFC.Model.SetTheory.Internal.Quotient

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
