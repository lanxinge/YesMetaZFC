import YesMetaZFC.Model.SetTheory.Internal.SourceTheory
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 原有界关系在源模型内的统一化

把固定关系编译成已支持的内部码，给参数构造实际赋值，再调用全代码统一化。
所得源内图直接满足背景中的原关系，供常值代表和函数求值使用。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_uniform_source_l {ω c X R D} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : BinarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) X)
    (hD : M.mem D X) (ht : ∀ x, M.mem x D → ∃ y, M.mem y X ∧ φ.denote ρ x y) :
    ∃ B C, M.mem B X ∧ M.mem C X ∧ Fn0_d D C B ∧ ∀ x y, Rd_entry_d x y B → φ.denote ρ x y := by
  obtain ⟨a, n, F, r, v, hF, hv, hc⟩ := source_compile_l I hZF hω φ.body φ.freeClosed
  have hinj : Function.Injective v := fun i j he => Fin.ext (num_injective_l (ZF.modelsKP hZF) (hv i) (he.symm ▸ hv j))
  have hωv i := num_mem_l hZF.1 hω (hv i)
  obtain ⟨z, hz⟩ := hm.1.2.1
  let η := (ρ.push z).push z
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, hp⟩ := senv_params_l I hZF hE hm.1.2.1 v η.bound hinj hωv (Fin.cases hz (Fin.cases hz hρ))
  have h10 : v 1 ≠ v 0 := fun h => by have e := congrArg Fin.val (hinj h); simp at e
  have read x y (hx : M.mem x X) (hy : M.mem y X) :
      Sbin_d I X R E F n r (v 1) (v 0) f x y ↔ φ.denote ρ x y := by
    obtain ⟨g, hg, hgf⟩ := senv_update_exists_l I hZF ((hE f).mp hf) (hωv 1) hx
    obtain ⟨k, hk, hkf⟩ := senv_update_exists_l I hZF hgf (hωv 0) hy
    have params : ∀ i, M.PairMember I (v i) (((ρ.push x).push y).bound i) k := Fin.cases
      ((hk.2 (v 0) y).mpr (Or.inl ⟨rfl, rfl⟩)) (Fin.cases
        ((hk.2 (v 1) x).mpr (Or.inr ⟨h10, (hg.2 (v 1) x).mpr (Or.inl ⟨rfl, rfl⟩)⟩)) (fun i => by
          have h0 : v i.succ.succ ≠ v 0 := fun h => Fin.succ_ne_zero i.succ (hinj h)
          have h1 : v i.succ.succ ≠ v 1 := fun h => Fin.succ_ne_zero i (Fin.succ_inj.mp (hinj h))
          exact (hk.2 _ _).mpr (Or.inr ⟨h0, (hg.2 _ _).mpr (Or.inr ⟨h1, hp i.succ.succ⟩)⟩)))
    exact (sbin_value_l I hZF.1 hg hk).trans
      (hc.delta_l I φ.freeClosed hd ((ρ.push x).push y) hX hm hE ((hE k).mpr hkf) params)
  obtain ⟨B, C, hBX, hCX, hBC, select⟩ := theory.uniformization E F n r (v 1) (v 0) f D hE hF.2.1 hF.2.2
    (hωv 1) (hωv 0) h10 hf hD (fun x hx => (ht x hx).imp fun y hy =>
      ⟨hy.1, (read x y (hX D hD x hx) hy.1).mpr hy.2⟩)
  exact ⟨B, C, hBX, hCX, hBC, fun x y hxy =>
    (read x y (hX D hD x (hBC.bound_l hxy).1) (hX C hCX y (hBC.bound_l hxy).2)).mp (select x y hxy)⟩

/-- 每个源对象都有实际源内常值代表，并保留源内值域界。 -/
theorem sc_constant_l {ω c X R D x} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hx : M.mem x X) : ∃ g C, M.mem g X ∧ M.mem C X ∧ Fn0_d D C g ∧
      ∀ a y, Rd_entry_d a y g ↔ M.mem a D ∧ y = x := by
  let φ : BinarySchema 1 := { body := Formula.extensionalEq .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  have sat a y : φ.denote ρ a y ↔ y = x := Formula.satisfies_extensionalEq_iff_eq hZF.1 ..
  obtain ⟨g, C, hg, hC, hf, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ (.atom _ _ _)
    ρ (fun _ => hx) hD (fun a _ => ⟨x, hx, (sat a x).mpr rfl⟩)
  refine ⟨g, C, hg, hC, hf, fun a y => ⟨fun h => ⟨(hf.bound_l h).1, (sat a y).mp (hs a y h)⟩, ?_⟩⟩
  rintro ⟨ha, rfl⟩
  obtain ⟨y, _, hy⟩ := hf.2.1 a ha
  exact (sat a y).mp (hs a y hy) ▸ hy

/-- 已在源中的函数图也有源内值域界，因而属于代码化函数域。 -/
theorem sc_function_domain_l {ω c X R D F} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hF : M.mem F X) (hf : Fn0_d D X F) : Sfun_d X D F := by
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  have sat x y : φ.denote ρ x y ↔ Rd_entry_d x y F := rd_entry0_sat_l hZF.1 ..
  obtain ⟨g, C, _, hC, hg, hs⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_entry0_delta_l ..)
    ρ (fun _ => hF) hD (fun x hx => (hf.2.1 x hx).imp fun y hy => ⟨hy.1, (sat x y).mpr hy.2⟩)
  have select x y (hxy : Rd_entry_d x y g) := (sat x y).mp (hs x y hxy)
  have eq : g = F := (fn0_function_l (ZF.modelsKP hZF) hg).1.1.eq_of_pairMember_iff hZF.1
    (fn0_function_l (ZF.modelsKP hZF) hf).1.1 (fun x y => ⟨select x y, fun hxy => by
      obtain ⟨z, _, hxz⟩ := hg.2.1 x (hf.bound_l hxy).1
      exact hf.2.2 x (hf.bound_l hxy).1 z (hf.bound_l (select x z hxz)).2 y (hf.bound_l hxy).2
        (select x z hxz) hxy ▸ hxz⟩)
  exact ⟨hF, C, hC, eq ▸ hg⟩

/-- 逐项读取源内函数图的首坐标，再分离出精确的定义域。 -/
theorem sc_function_domain_mem_l {ω c X R A B F : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hF : M.mem F X) (hf : Fn0_d A B F) : M.mem A X := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => F⟩
  let φ : BinarySchema 0 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem .newest (kpair0_m (.bound 3) (.bound 2) .newest)) }
  have sat p a : φ.denote ρ p a ↔ ∃ t, M.mem t p ∧ ∃ b, M.mem b t ∧ KPair_d M p a b := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨g, C, _, hCX, hg, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ
    (.existsMem _ (.existsMem _ (kpair0_delta_l ..))) ρ (fun i => Fin.elim0 i) hF (fun p hp => by
      obtain ⟨a, _, b, _, hab⟩ := hf.1 p hp
      obtain ⟨t, ht, hb⟩ := (kpair_union_l M hab b).mpr (Or.inr rfl)
      exact ⟨a, (rd_entry_transitive_l hX hF ⟨p, hab, hp⟩).1, (sat p a).mpr ⟨t, ht, b, hb, hab⟩⟩)
  have bound a (ha : M.mem a A) : M.mem a C := by
    obtain ⟨b, _, p, hp, hpf⟩ := hf.2.1 a ha
    obtain ⟨v, hv, hpv⟩ := hg.2.1 p hpf
    obtain ⟨_, _, w, _, hp'⟩ := (sat p v).mp (select p v hpv)
    exact (kpair_injective_l M hp' hp).1 ▸ hv
  let η : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let ψ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1) (Formula.existsMem .newest
      (Formula.existsMem .newest (kpair0_m (.bound 2) (.bound 3) .newest))) }
  have read a : ψ.denote η a ↔ ∃ p, M.mem p F ∧ ∃ t, M.mem t p ∧ ∃ b, M.mem b t ∧ KPair_d M p a b := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  obtain ⟨D, hDX, spec⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) η (fun _ => hF) hCX
  have eq : D = A := hZF.1.eq_of_same_members D A (fun a => by
    rw [spec a, read a]
    refine ⟨fun ⟨_, p, hp, _, _, b, _, hab⟩ => (hf.bound_l ⟨p, hab, hp⟩).1, fun ha => ?_⟩
    obtain ⟨b, _, p, hp, hpf⟩ := hf.2.1 a ha
    obtain ⟨t, ht, hb⟩ := (kpair_union_l M hp b).mpr (Or.inr rfl)
    exact ⟨bound a ha, p, hpf, t, ht, b, hb, hp⟩)
  exact eq ▸ hDX

end YesMetaZFC.SetTheory.Internal
