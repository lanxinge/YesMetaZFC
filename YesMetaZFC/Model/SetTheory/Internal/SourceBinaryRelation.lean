import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 任意内部二元程序的源内真值图

在原程序后追加有序对模板及两个存在量词，再对源内乘积作分离。
新增坐标严格位于原支撑外，故既覆盖非标准程序，也保留原参数赋值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_binary_relation_l {ω c X R E F n r i j f D C : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hE : M.IsFunctionSpace I E ω X) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hj : M.mem j ω) (hij : i ≠ j) (hf : M.mem f E)
    (hD : M.mem D X) (hC : M.mem C X) : ∃ Q, M.mem Q X ∧ M.IsSetRelation I Q ∧
      ∀ x y, Rd_entry_d x y Q ↔ M.mem x D ∧ M.mem y C ∧ Sbin_d I X R E F n r i j f x y := by
  obtain ⟨s, hs, bound, his, hjs⟩ := sbound_above_l I hZF hω hF hi hj
  obtain ⟨σ, step, hσ⟩ := hω.1.2 s hs
  have into x (hx : M.mem x s) : M.mem x σ := (step x).mpr (Or.inl hx)
  have ir := KP.mem_irrefl_d (ZF.modelsKP hZF)
  have hsi : s ≠ i := fun e => ir i (e ▸ his)
  have hsj : s ≠ j := fun e => ir j (e ▸ hjs)
  let φ : Formula 1 3 := kpair0_m .newest (.bound 1) (.bound 2)
  let a : Fin 3 → M.Domain := Fin.cases s (Fin.cases i (fun _ => j))
  obtain ⟨n₁, F₁, r₁, b₁, read₁⟩ := sfm_delta_l I hZF hω hF φ
    (by simp -implicitDefEqProofs [φ]) (kpair0_delta_l ..) a hσ
    (Fin.cases step.predecessor_mem (Fin.cases (into i his) (fun _ => into j hjs)))
  obtain ⟨n₂, F₂, r₂, b₂, read₂⟩ := sfm_and_l I hZF hω b₁.program b₁.root (b₁.span r hr)
  obtain ⟨n₃, F₃, r₃, b₃, read₃⟩ := sfm_ex_l I hZF hω b₂.program hj b₂.root
  obtain ⟨m, G, k, build, read⟩ := sfm_ex_l I hZF hω b₃.program hi b₃.root
  have point p (hp : M.mem p X) g (ug : Senv_update_d I f s p g) :
      Ssat_d I X R E G m k g ↔ ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧
        KPair_d M p x y ∧ Sbin_d I X R E F n r i j f x y := by
    have fg := ug.function_l I ((hE f).mp hf) hs hp
    have hg := (hE g).mpr fg
    have matrix x (hx : M.mem x X) v (uv : Senv_update_d I g i x v)
        y (hy : M.mem y X) w (uw : Senv_update_d I v j y w) :
        Ssat_d I X R E F₂ n₂ r₂ w ↔ KPair_d M p x y ∧ Sbin_d I X R E F n r i j f x y := by
      have hw := (hE w).mpr (uw.function_l I (uv.function_l I fg hi hx) hj hy)
      let ρ : Env M 3 := ⟨Fin.cases p (Fin.cases x (fun _ => y)), fun _ => p⟩
      have atom := (read₁ X R E c w ρ hX hm hE hw (Fin.cases
        ((uw.2 s p).mpr (Or.inr ⟨hsj, (uv.2 s p).mpr (Or.inr ⟨hsi, (ug.2 s p).mpr (Or.inl ⟨rfl, rfl⟩)⟩)⟩))
        (Fin.cases ((uw.2 i x).mpr (Or.inr ⟨hij, (uv.2 i x).mpr (Or.inl ⟨rfl, rfl⟩)⟩))
          (fun _ => (uw.2 j y).mpr (Or.inl ⟨rfl, rfl⟩))))).trans (kpair0_sat_l hZF.1 ρ .newest (.bound 1) (.bound 2))
      have truth : Sbin_d I X R E F n r i j f x y ↔ Ssat_d I X R E F n r w :=
        (sbin_agree_l I hZF hF bound hr hi hj hE hf hg (ug.agree_l I (ir s)) hx hy).trans
        (sbin_value_l I hZF.1 uv uw)
      rw [read₂ X R E w hw, ← b₁.sat_l I hZF hF hr X R E w]
      exact and_congr atom truth.symm
    rw [read X R E g hg]
    constructor
    · rintro ⟨x, v, hx, uv, ht⟩
      obtain ⟨y, w, hy, uw, ht⟩ := (read₃ X R E v ((hE v).mpr (uv.function_l I fg hi hx))).mp ht
      exact ⟨x, hx, y, hy, (matrix x hx v uv y hy w uw).mp ht⟩
    · rintro ⟨x, hx, y, hy, ht⟩
      obtain ⟨v, uv, fv⟩ := senv_update_exists_l I hZF fg hi hx
      obtain ⟨w, uw, _⟩ := senv_update_exists_l I hZF fv hj hy
      exact ⟨x, v, hx, uv, (read₃ X R E v ((hE v).mpr fv)).mpr
        ⟨y, w, hy, uw, (matrix x hx v uv y hy w uw).mpr ht⟩⟩
  obtain ⟨P, hP, product⟩ := theory.algebra.product D C hD hC
  obtain ⟨Q, hQ, sep⟩ := theory.separation E G m k s f P hE build.program build.root hs hf hP
  have spec p : M.mem p Q ↔ M.mem p P ∧ ∃ x, M.mem x X ∧ ∃ y, M.mem y X ∧
      KPair_d M p x y ∧ Sbin_d I X R E F n r i j f x y := by
    apply (sep p).trans
    apply and_congr_right
    intro hp
    refine ⟨fun ⟨g, ug, ht⟩ => (point p (hX P hP p hp) g ug).mp ht, fun ht => ?_⟩
    obtain ⟨g, ug, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hs (hX P hP p hp)
    exact ⟨g, ug, (point p (hX P hP p hp) g ug).mpr ht⟩
  refine ⟨Q, hQ, fun p hp => ?_, fun x y => ⟨?_, ?_⟩⟩
  · obtain ⟨x, _, y, _, pair⟩ := (product p).mp ((spec p).mp hp).1
    exact ⟨x, y, pair⟩
  · rintro ⟨p, pair, hp⟩
    obtain ⟨hp, a, _, b, _, pair', ht⟩ := (spec p).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    obtain ⟨a, ha, b, hb, pair'⟩ := (product p).mp hp
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M pair' pair
    exact ⟨ha, hb, ht⟩
  · rintro ⟨hx, hy, ht⟩
    obtain ⟨p, pair⟩ := (I).total x y
    exact ⟨p, pair, (spec p).mpr ⟨(product p).mpr ⟨x, hx, y, hy, pair⟩,
      x, hX D hD x hx, y, hX C hC y hy, pair, ht⟩⟩

end YesMetaZFC.SetTheory.Internal
