import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 任意内部二元程序的原关系真值图

在原程序后追加有序对模板及两个存在量词，再对模型内实际乘积作分离。
所有见证都是同一原关系中的对象；只用外延性、配对及给定乘积。
新增坐标严格位于原支撑外，覆盖非标准内部程序并保留原参数赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_binary_relation_l {ω c X R E F n r i j f : M.Domain} (hω : M.IsOmega ω)
    (hm : Smdl_d I c X R) (ext : Extensional (smdl_structure_l I (R := R) hm.2.1))
    (J : kpair_convention_l.Interpretation (smdl_structure_l I (R := R) hm.2.1))
    (separate : ∀ E F n r i f D, M.IsFunctionSpace I E ω X → Sfm_d I ω n F → M.mem r n →
      M.mem i ω → M.mem f E → M.mem D X → ∃ A, M.mem A X ∧ Sr_sep_d I X R E F n r i f D A)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E)
    (D C P : (smdl_structure_l I (R := R) hm.2.1).Domain)
    (product : (smdl_structure_l I (R := R) hm.2.1).IsCartesianProduct J P D C) :
    ∃ Q : (smdl_structure_l I (R := R) hm.2.1).Domain,
      (smdl_structure_l I (R := R) hm.2.1).IsSetRelation J Q ∧
      ∀ x y : (smdl_structure_l I (R := R) hm.2.1).Domain, Rd_entry_d x y Q ↔
        (smdl_structure_l I (R := R) hm.2.1).mem x D ∧
        (smdl_structure_l I (R := R) hm.2.1).mem y C ∧ Sbin_d I X R E F n r i j f x.val y.val := by
  let N := smdl_structure_l I (R := R) hm.2.1
  have codes {p x y : N.Domain} : J.Codes p x y ↔ KPair_d N p x y :=
    (J.satisfies_code_iff (⟨fun k => [p,x,y].get k, fun _ => p⟩ : Env N 3)
      (.bound 0) (.bound 1) (.bound 2)).symm.trans (kpair_sat_l N ext _ _ _ _)
  obtain ⟨s, hs, bound, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨σ, step, hσ⟩ := hω.1.2 s hs
  have into x (hx : M.mem x s) : M.mem x σ := (step x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun e => ir i (e ▸ his)
  have hsj : s ≠ j := fun e => ir j (e ▸ hjs)
  let φ : Formula 1 3 := kpair0_m .newest (.bound 1) (.bound 2)
  let a : Fin 3 → M.Domain := Fin.cases s (Fin.cases i (fun _ => j))
  obtain ⟨n₁, F₁, r₁, b₁, read₁⟩ := sfm_template_l I hZF hω hF φ
    (by simp -implicitDefEqProofs [φ]) a hσ
    (Fin.cases step.predecessor_mem (Fin.cases (into i his) (fun _ => into j hjs)))
  obtain ⟨n₂, F₂, r₂, b₂, read₂⟩ := sfm_and_l I hZF hω b₁.program b₁.root (b₁.span r hr)
  obtain ⟨n₃, F₃, r₃, b₃, read₃⟩ := sfm_ex_l I hZF hω b₂.program hj b₂.root
  obtain ⟨m, G, k, build, read⟩ := sfm_ex_l I hZF hω b₃.program hi b₃.root
  have point (p : N.Domain) g (ug : Senv_update_d I f s p.val g) :
      Ssat_d I X R E G m k g ↔ ∃ x y : N.Domain,
        KPair_d N p x y ∧ Sbin_d I X R E F n r i j f x.val y.val := by
    have fg := ug.function_l I ((hE f).mp hf) hs p.property
    have hg := (hE g).mpr fg
    have matrix (x : N.Domain) v (uv : Senv_update_d I g i x.val v)
        (y : N.Domain) w (uw : Senv_update_d I v j y.val w) :
        Ssat_d I X R E F₂ n₂ r₂ w ↔ KPair_d N p x y ∧ Sbin_d I X R E F n r i j f x.val y.val := by
      have hw := (hE w).mpr (uw.function_l I (uv.function_l I fg hi x.property) hj y.property)
      let ρ : Env N 3 := ⟨Fin.cases p (Fin.cases x (fun _ => y)), fun _ => p⟩
      have atom := (read₁ X R hm.2.1 E hE w hw ρ (Fin.cases
        ((uw.2 s p.val).mpr (Or.inr ⟨hsj, (uv.2 s p.val).mpr (Or.inr ⟨hsi, (ug.2 s p.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩))
        (Fin.cases ((uw.2 i x.val).mpr (Or.inr ⟨hij, (uv.2 i x.val).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
          (fun _ => (uw.2 j y.val).mpr (Or.inl ⟨rfl, rfl⟩))))).trans (kpair0_sat_l ext ρ .newest (.bound 1) (.bound 2))
      have truth : Sbin_d I X R E F n r i j f x.val y.val ↔ Ssat_d I X R E F n r w :=
        (sbin_agree_l I hZF hF bound hr hi hj hE hf hg (ug.agree_l I (ir s)) x.property y.property).trans
        (sbin_value_l I hZF.1 uv uw)
      rw [read₂ X R E w hw, ← b₁.sat_l I hZF hF hr X R E w]
      exact and_congr atom truth.symm
    rw [read X R E g hg]
    constructor
    · rintro ⟨x, v, hx, uv, ht⟩
      obtain ⟨y, w, hy, uw, ht⟩ := (read₃ X R E v ((hE v).mpr (uv.function_l I fg hi hx))).mp ht
      exact ⟨⟨x, hx⟩, ⟨y, hy⟩, (matrix ⟨x, hx⟩ v uv ⟨y, hy⟩ w uw).mp ht⟩
    · rintro ⟨x, y, ht⟩
      obtain ⟨v, uv, fv⟩ := senv_update_exists_l I hZF fg hi x.property
      obtain ⟨w, uw, _⟩ := senv_update_exists_l I hZF fv hj y.property
      exact ⟨x.val, v, x.property, uv, (read₃ X R E v ((hE v).mpr fv)).mpr
        ⟨y.val, w, y.property, uw, (matrix x v uv y w uw).mpr ht⟩⟩
  obtain ⟨Q, hQ, sep⟩ := separate E G m k s f P.val hE build.program build.root hs hf P.property
  let Q₀ : N.Domain := ⟨Q, hQ⟩
  have spec (p : N.Domain) : N.mem p Q₀ ↔ N.mem p P ∧ ∃ x y : N.Domain,
      KPair_d N p x y ∧ Sbin_d I X R E F n r i j f x.val y.val := by
    apply (sep p.val p.property).trans
    apply and_congr_right
    intro _
    refine ⟨fun ⟨g, ug, ht⟩ => (point p g ug).mp ht, fun ht => ?_⟩
    obtain ⟨g, ug, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs p.property
    exact ⟨g, ug, (point p g ug).mpr ht⟩
  refine ⟨Q₀, fun p hp => ?_, fun x y => ⟨?_, ?_⟩⟩
  · obtain ⟨x, _, y, _, pair⟩ := (product p).mp ((spec p).mp hp).1
    exact ⟨x, y, pair⟩
  · rintro ⟨p, pair, hp⟩
    obtain ⟨hp, a, b, pair', ht⟩ := (spec p).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l N pair' pair
    obtain ⟨a, ha, b, hb, pair'⟩ := (product p).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l N (codes.mp pair') pair
    exact ⟨ha, hb, ht⟩
  · rintro ⟨hx, hy, ht⟩
    obtain ⟨p, pair⟩ := J.total x y
    exact ⟨p, codes.mp pair, (spec p).mpr ⟨(product p).mpr ⟨x, hx, y, hy, pair⟩, x, y, codes.mp pair, ht⟩⟩

end YesMetaZFC.SetTheory.Internal
