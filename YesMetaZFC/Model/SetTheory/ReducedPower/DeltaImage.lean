import YesMetaZFC.Model.SetTheory.ReducedPower.Restriction
import YesMetaZFC.Model.SetTheory.ReducedPower.RelationFormulaImage

/-! # 未坍塌商及其关系像中的完整公式 Łoś

目标保留原关系结构，量词始终在该结构中解释。源内真值集和实际代表赋值
仍由原内部 Łoś 构造；不要求目标良基、传递或具有背景中的全部函数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_formula_image_l {ω a X R D U c G p C T d Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I a X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) (model : Rp_model_d I D X U R c G p C T)
    (target : Smdl_d I d Y S) (hj : Smap_d I ω c d C Y j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed)
    (f : Fin n → M.Domain) (hf : ∀ i, M.mem (f i) G)
    (ρ : Env (smdl_structure_l I (R := S) target.2.1) n)
    (values : ∀ i, ∃ B, Rd_entry_d (f i) B p ∧ Rd_entry_d B (ρ.bound i).val j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A X ∧ M.mem A U ∧ M.MemberSubset A D ∧
      ∀ v, M.mem v A → ∀ η : Env (smdl_structure_l I (R := R) hm.1.2.1) n,
        (∀ i, Rd_entry_d v (η.bound i).val (f i)) → Formula.satisfies η φ := by
  obtain ⟨P, U', hp, hu, us, md⟩ := rs_restrict_model_l hZF hω hX hm theory hD hU hG model
  obtain ⟨t, ft₀, id⟩ := fn0_identity_l (ZF.modelsKP hZF) D
  have ft := ft₀.mono_target_l (hX D hD)
  have domain s x (hsx : Rd_entry_d s x t) : Rd_entry_d x D R := by
    obtain ⟨hs, rfl⟩ := (id s x).mp hsx
    exact (hm.2 s D).mpr ⟨hX D hD s hs, hD, hs⟩
  have decode {f} (hf : M.mem f X) : Rc_graph_d I X R t f f := by
    intro s x y hsx
    obtain ⟨_, rfl⟩ := (id s x).mp hsx
    exact (rf_val_mem_l I hZF.1 hX hm hf).symm
  have family : Rc_family_d I X R D D t G := by
    intro g
    constructor
    · intro hg
      obtain ⟨hx, fg⟩ := (hG g).mp hg
      exact ⟨fg, g, (rf_fun_mem_l I hZF.1 hX hm hD).mpr
        (sc_function_domain_l (theory.algebra_l I (ZF.modelsKP hZF) hX hm) hx fg), decode hx⟩
    · rintro ⟨fg, f, ff, graph⟩
      have sf := (rf_fun_mem_l I hZF.1 hX hm hD).mp ff
      have eq := graph.unique_l I hZF.1 ft fg (sf.function_l hX) (decode sf.1)
      exact (hG g).mpr ⟨eq.symm ▸ sf.1, fg⟩
  -- 隶属源的全部迹正是原源子集族；交集仍由原分离证书产生。
  have source : Rt_source_d I X R D t P := by
    intro A
    constructor
    · intro hA
      obtain ⟨hAX, sub⟩ := (hp A).mp hA
      refine ⟨A, hAX, fun s => ⟨?_, ?_⟩⟩
      · intro hs
        exact ⟨sub s hs, s, (id s s).mpr ⟨sub s hs, rfl⟩, (hm.2 s A).mpr ⟨hX A hAX s hs, hAX, hs⟩⟩
      · rintro ⟨_, x, hsx, hxA⟩
        exact ((id s x).mp hsx).2 ▸ ((hm.2 x A).mp hxA).2.2
    · rintro ⟨B, hB, trace⟩
      let ψ : UnarySchema 1 := { body := .mem .newest (.bound 1) }
      let ε : Env M 1 := ⟨fun _ => B, fun _ => B⟩
      obtain ⟨A', hA', sep⟩ := sc_separate_source_l I hZF hω hX hm theory ψ (.mem ..) ε (fun _ => hB) hD
      have eq : A = A' := by
        apply hZF.1.eq_of_same_members
        intro s
        apply (trace s).trans (Iff.trans ?_ (sep s).symm)
        change (M.mem s D ∧ ∃ x, Rd_entry_d s x t ∧ Rd_entry_d x B R) ↔ (M.mem s D ∧ M.mem s B)
        constructor
        · rintro ⟨hs, x, hsx, hxB⟩
          exact ⟨hs, ((id s x).mp hsx).2 ▸ ((hm.2 x B).mp hxB).2.2⟩
        · rintro ⟨hs, hsB⟩
          exact ⟨hs, s, (id s s).mpr ⟨hs, rfl⟩, (hm.2 s B).mpr ⟨hX D hD s hs, hB, hsB⟩⟩
      exact (hp A).mpr ⟨eq.symm ▸ hA', fun s hs => ((trace s).mp hs).1⟩
  have los := rc_formula_image_l hZF hω hm.1 (rf_ext_mem_l I hZF.1 hX hm) theory
    ⟨D, hD⟩ uniform ft domain source hu family md target hj
    φ hφ f f (fun i => (rf_fun_mem_l I hZF.1 hX hm hD).mpr
      (sc_function_domain_l (theory.algebra_l I (ZF.modelsKP hZF) hX hm) ((hG (f i)).mp (hf i)).1 ((hG (f i)).mp (hf i)).2))
    hf (fun i => decode ((hG (f i)).mp (hf i)).1) ρ values
  refine los.trans ⟨?_, ?_⟩
  · rintro ⟨A, hA, holds⟩
    obtain ⟨hAP, hAU⟩ := (us A).mp hA
    exact ⟨A, ((hp A).mp hAP).1, hAU, hu.base.bounds A hA, holds⟩
  · rintro ⟨A, hAX, hAU, sub, holds⟩
    exact ⟨A, (us A).mpr ⟨(hp A).mpr ⟨hAX, sub⟩, hAU⟩, holds⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 完整关系 Łoś 在传递像中的有界解码

商计算全部交给一般关系版本；这里仅在源端和目标端使用 Δ₀ 绝对性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_delta_image_l {ω a X R D U c G p C T d Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I a X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) (model : Rp_model_d I D X U R c G p C T)
    (hY : M.TransitiveSet Y) (target : Smem_d I d Y S) (hj : Smap_d I ω c d C Y j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (hd : φ.IsDelta0)
    (f : Fin n → M.Domain) (hf : ∀ i, M.mem (f i) G) (ρ : Env M n)
    (values : ∀ i, ∃ B, Rd_entry_d (f i) B p ∧ Rd_entry_d B (ρ.bound i) j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A X ∧ M.mem A U ∧ M.MemberSubset A D ∧
      ∀ v, M.mem v A → ∀ η : Env M n, (∀ i, Rd_entry_d v (η.bound i) (f i)) → Formula.satisfies η φ := by
  obtain ⟨y, hy⟩ := target.1.2.1
  let θ : Env (smdl_structure_l I (R := S) target.1.2.1) n :=
    ⟨fun i => ⟨ρ.bound i, (values i).elim fun _ h => hj.1.1.output_mem_of_pairMember h.2⟩, fun _ => ⟨y, hy⟩⟩
  have read : Formula.satisfies θ φ ↔ Formula.satisfies ρ φ :=
    (smem_delta_image_l I target hY hd θ).trans (Formula.closed_env_l φ hφ rfl)
  have los := rs_formula_image_l hZF hω hX hm theory uniform hD hU hG model target.1 hj φ hφ f hf θ values
  refine read.symm.trans (los.trans ?_)
  apply exists_congr
  intro A
  apply and_congr_right
  intro hAX
  apply and_congr_right
  intro hAU
  apply and_congr_right
  intro hAD
  constructor
  · intro holds s hs η entries
    obtain ⟨x, hx⟩ := hm.1.2.1
    let η' : Env (smdl_structure_l I (R := R) hm.1.2.1) n :=
      ⟨fun i => ⟨η.bound i, ((hG (f i)).mp (hf i)).2.bound_l (entries i) |>.2⟩, fun _ => ⟨x, hx⟩⟩
    exact (Formula.closed_env_l φ hφ (ρ := image_env_l Subtype.val η') (η := η) rfl).mp
      ((smem_delta_image_l I hm hX hd η').mp (holds s hs η' entries))
  · intro holds s hs η entries
    exact (smem_delta_image_l I hm hX hd η).mpr
      (holds s hs ⟨fun i => (η.bound i).val, fun i => (η.free i).val⟩ entries)

end YesMetaZFC.SetTheory.Internal
