import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationBounded
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 原关系商中低层成员的处处有界代表

只在测度零处改值。改后的函数码由原源的有界统一化构造并传输，
因而仍属于同一原关系源；再由原子 Łoś 识别同一个商元素。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_bound_raw_l {ω c X R c' Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (ext : Rf_ext_d I Y S) (d b a f z : (smdl_structure_l I (R := S) model.2.1).Domain)
    (ff : Fn0_d d b f) (hz : Rd_entry_d z.val a.val S) :
    ∃ g : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d d a g ∧
      ∀ x y, Rd_entry_d x.val d.val S → Rd_entry_d y.val a.val S → Rd_entry_d x y f → Rd_entry_d x y g := by
  let χ : Formula 1 6 := .conj (fn0_m (.bound 5) (.bound 3) .newest)
    (Formula.forallMem (.bound 5) (Formula.forallMem (.bound 4)
      (.imp (rd_entry0_m (.bound 1) .newest (.bound 4)) (rd_entry0_m (.bound 1) .newest (.bound 2)))))
  let ψ : Formula 1 5 := .imp (.conj (fn0_m (.bound 4) (.bound 3) (.bound 1)) (.mem .newest (.bound 2))) (.existsE χ)
  let φ : Formula 1 0 := Formula.forallClosure 5 ψ
  obtain ⟨x₀, hx₀⟩ := hm.1.2.1
  let ρ : Env (smdl_structure_l I (R := R) hm.1.2.1) 0 := ⟨Fin.elim0, fun _ => ⟨x₀, hx₀⟩⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 0 := ⟨Fin.elim0, fun _ => d⟩
  have valid : Formula.satisfies ρ φ := by
    apply (smem_formula_l I hm ⟨⟨x₀, hx₀⟩⟩ φ ⟨ρ.bound, ρ.free⟩).mp
    apply (Formula.satisfies_forallClosure_iff _ ψ).mpr
    intro v
    simp only [ψ, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff]
    intro pre
    have pre := (rt_model_delta_l hX _ (.conj (fn0_delta_l ..) (.mem ..)) _).mp pre
    simp only [Formula.satisfies_conj_iff, fn0_sat_l hZF.1, Formula.satisfies_mem_iff] at pre
    let ξ : BinarySchema 3 := {
      body := .disj (.conj (.mem .newest (.bound 3)) (rd_entry0_m (.bound 1) .newest (.bound 2)))
        (.conj (.neg (Formula.existsMem (.bound 3) (rd_entry0_m (.bound 2) .newest (.bound 3))))
          (Formula.extensionalEq .newest (.bound 4))) }
    let τ : Env M 3 := ⟨Fin.cases (v 1).val (Fin.cases (v 2).val (fun _ => (v 0).val)), fun _ => (v 0).val⟩
    have sat x y : ξ.denote τ x y ↔ (M.mem y (v 2).val ∧ Rd_entry_d x y (v 1).val) ∨
        (¬ (∃ w, M.mem w (v 2).val ∧ Rd_entry_d x w (v 1).val) ∧ y = (v 0).val) := by
      simp only [ξ, BinarySchema.denote, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
        Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_neg_iff,
        Formula.satisfies_existsMem_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]; rfl
    obtain ⟨g, hg, fg, select⟩ := sc_uniform_source_l hZF hω hX hm theory ξ
      (.disj (.conj (.mem ..) (rd_entry0_delta_l ..)) (.conj (.neg (.existsMem _ (rd_entry0_delta_l ..))) (.atom ..)))
      τ (Fin.cases (v 1).property (Fin.cases (v 2).property (fun _ => (v 0).property))) (v 4).property (v 2).property (fun x _ => by
        classical
        by_cases h : ∃ y, M.mem y (v 2).val ∧ Rd_entry_d x y (v 1).val
        · obtain ⟨y, hy, hxy⟩ := h
          exact ⟨y, hy, (sat x y).mpr (Or.inl ⟨hy, hxy⟩)⟩
        · exact ⟨(v 0).val, pre.2, (sat x (v 0).val).mpr (Or.inr ⟨h, rfl⟩)⟩)
    refine ⟨⟨g, hg⟩, (rt_model_delta_l hX _ (.conj (fn0_delta_l ..)
      (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..))))) _).mpr ?_⟩
    simp only [Formula.satisfies_conj_iff, fn0_sat_l hZF.1, Formula.satisfies_forallMem_iff,
      Formula.satisfies_imp_iff, rd_entry0_sat_l hZF.1]
    refine ⟨fg, fun x hx y hy hxy => ?_⟩
    obtain ⟨w, _, hxw⟩ := fg.2.1 x hx
    rcases (sat x w).mp (select x w hxw) with ⟨_, hxw'⟩ | ⟨no, _⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) pre.1).1.2 x w y hxw' hxy ▸ hxw
    · exact (no ⟨y, hy, hxy⟩).elim
  have moved := (smap_source_l I hZF hω hm.1 model hq φ
    (by simp -implicitDefEqProofs [φ, ψ, χ, Formula.forallClosure, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)).mp valid
  have result := (Formula.satisfies_forallClosure_iff _ ψ).mp moved
    (Fin.cases z (Fin.cases f (Fin.cases a (Fin.cases b (fun _ => d)))))
  simp only [ψ, χ, Formula.satisfies_imp_iff, Formula.satisfies_conj_iff, fn0_sat_l (ext.native_l I model.2.1),
    Formula.satisfies_mem_iff, Formula.satisfies_exists_iff, Formula.satisfies_forallMem_iff,
    rd_entry0_sat_l (ext.native_l I model.2.1)] at result
  obtain ⟨g, fg, keep⟩ := result ⟨ff, hz⟩
  exact ⟨g, fg, fun x y hx hy h => keep x hx y hy h⟩

theorem rc_bounded_representative_l {ω c X R c' Y S q D t U G o p C T a A E : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (d : (smdl_structure_l I (R := S) source.2.1).Domain) (ft : Fn0_d D Y t)
    (domain : ∀ s x, Rd_entry_d s x t → Rd_entry_d x d.val S)
    (hU : Base_d D U) (proper : Proper_d U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T)
    (value : M.mem a Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D a f ∧ Rd_entry_d f A p)
    (edge : Rd_entry_d E A T) :
    ∃ g, M.mem g G ∧ Rd_entry_d g E p ∧ ∀ s y, Rd_entry_d s y g → Rd_entry_d y a S := by
  have ext : Rf_ext_d I Y S := hq.extensional_l hZF hω hm.1 source (rf_ext_mem_l I hZF.1 hX hm)
  obtain ⟨ha, k, hk, constant, hkA⟩ := value
  obtain ⟨f, hfE⟩ := (model.map.range E).mp (model.code.2.2.2 E A edge).1
  obtain ⟨_, B, F, ff, decode⟩ := (hG f).mp (model.map.projection.input_mem_of_pairMember hfE)
  obtain ⟨P, hP, point⟩ := (model.relation f k E A hfE hkA).mp edge
  have bounded s (hs : M.mem s P) : ∃ y, M.mem y Y ∧ Rd_entry_d s y f ∧ Rd_entry_d y a S := by
    obtain ⟨y, hy, z, _, hsy, hsz, hyz⟩ := point s hs
    have eq := (fn0_function_l (ZF.modelsKP hZF) (model.map.functions k hk)).1.2 s z a hsz (constant s (hU.bounds P hP s hs))
    exact ⟨y, hy, hsy, eq ▸ hyz⟩
  obtain ⟨s₀, hs₀⟩ := proper P hP
  obtain ⟨z, hz, _, hza⟩ := bounded s₀ hs₀
  obtain ⟨F', ff', agree⟩ := sc_bound_raw_l hZF hω hX hm theory source hq ext d B ⟨a, ha⟩ F ⟨z, hz⟩ ff hza
  obtain ⟨g, gg, decode'⟩ := smdl_function_l hZF source ext d ⟨a, ha⟩ F' ff' ft domain
  have hg := (hG g).mpr ⟨gg, ⟨a, ha⟩, F', ff', decode'⟩
  obtain ⟨E', _, hgE⟩ := model.map.projection.2.2 g hg
  have eq : E = E' := (rp_kernel_l I hZF.1 hU model.map hfE hgE).mpr ⟨P, hP, fun s hs => by
    obtain ⟨y, hy, hsy, hya⟩ := bounded s hs
    obtain ⟨x, hx, hsx⟩ := ft.2.1 s (hU.bounds P hP s hs)
    exact ⟨y, hy, hsy, (decode' s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mpr
      (agree ⟨x, hx⟩ ⟨y, hy⟩ (domain s x hsx) hya ((decode s ⟨x, hx⟩ ⟨y, hy⟩ hsx).mp hsy))⟩⟩
  refine ⟨g, hg, eq.symm ▸ hgE, fun s y hsy => ?_⟩
  obtain ⟨x, hx, hsx⟩ := ft.2.1 s (gg.bound_l hsy).1
  exact (ff'.bound_l ((decode' s ⟨x, hx⟩ ⟨y, (gg.bound_l hsy).2⟩ hsx).mp hsy)).2

/-- 下一商的低层恰由所属源中的有界图覆盖，包括全部新商成员。 -/
theorem Rp_model_d.low_cover_raw_l {ω c X R c' Y S q B H N Γ γ k D A t U G o p C T j A' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (source : Smdl_d I c' Y S) (hq : Smap_d I ω c c' X Y q)
    (hBH : Rd_entry_d B H q)
    (closed : ∀ a b, M.mem a B → M.mem b X → M.MemberSubset b a → M.mem b B)
    (hN : M.TransitiveSet N) (algebra : Sc_algebra_d N)
    (hΓN : M.mem Γ N) (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (d a : (smdl_structure_l I (R := S) source.2.1).Domain)
    (hD : Rd_entry_d D d.val k) (hA : Rd_entry_d A a.val k) (ht : M.IsRestrictionOf I t k D)
    (hU : Base_d D U) (proper : Proper_d U)
    (hG : ∀ g, M.mem g G ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) source.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) source.2.1).Domain), Rd_entry_d s x.val t →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model : Rp_model_d I D Y U S o G p C T)
    (constants : ∀ x B, Rd_entry_d x B j ↔ M.mem x Y ∧ ∃ f, M.mem f G ∧ Rs_const_d D x f ∧ Rd_entry_d f B p)
    (ha : Rd_entry_d a.val A' j) : ∀ E, Rd_entry_d E A' T ↔
      ∃ F g, M.mem F N ∧ Fn0_d D A F ∧ Cp0_d D Γ Y F k g ∧ Rd_entry_d g E p := by
  have trans := rank.transitive_l hZF hN hΓN
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo fk.1 (trans D (fk.1.input_mem_of_pairMember hD)))
  have domain s x (hsx : Rd_entry_d s x t) := (pred D d.val hD x).mpr
    ⟨s, ((ht.2 s x).mp hsx).1, ((ht.2 s x).mp hsx).2⟩
  have common := hq.bounded_functions_raw_l hZF hω hX hm source hBH closed hN algebra hΓN rank hγ fk image pred d a hD hA ht hG
  intro E
  constructor
  · intro edge
    obtain ⟨g, hg, hgE, bound⟩ := rc_bounded_representative_l hZF hω hX hm theory source hq d ft domain hU proper hG model
      ((constants a.val A').mp ha) edge
    obtain ⟨F, hF, fn, comp⟩ := (common g).mp ⟨hg, bound⟩
    exact ⟨F, g, hF, fn, comp, hgE⟩
  · rintro ⟨F, g, hF, fn, comp, hgE⟩
    obtain ⟨hg, bound⟩ := (common g).mpr ⟨F, hF, fn, comp⟩
    obtain ⟨_, f, _, constant, hfA⟩ := (constants a.val A').mp ha
    apply (model.relation g f E A' hgE hfA).mpr
    refine ⟨D, hU.top, fun s hs => ?_⟩
    obtain ⟨y, hy, hsy⟩ := (model.map.functions g hg).2.1 s hs
    exact ⟨y, hy, a.val, a.property, hsy, constant s hs, bound s y hsy⟩

end YesMetaZFC.SetTheory.Internal
