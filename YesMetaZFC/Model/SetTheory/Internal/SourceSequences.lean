import YesMetaZFC.Model.SetTheory.Internal.SourceFinite

/-! # 有限序列空间在后继模型中的实际保持

先传输每个字母表的内部序列空间，再用源内有限函数闭性证明它已包含
全部背景内部有限图；新字母表不必来自旧嵌入的像。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sc_sequences_d (I : kpair_convention_l.Interpretation M) (ω X : M.Domain) : Prop :=
  ∀ A, M.mem A X → ∃ K, M.mem K X ∧ Fseq_space_d I ω A K

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_sequences_forward_l {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hq : Smap_d I ω c d X Y q)
    (hωX : M.mem ω X) (source : Sc_sequences_d I ω X) (theory : Sc_theory_d I ω Y S) : Sc_sequences_d I ω Y := by
  have hωq := hq.omega_l I hZF hω hX hY hm hn hωX
  have hωY := hq.1.1.output_mem_of_pairMember hωq
  -- 固定句子 ∀A ∃K ∀f (f∈K ↔ ∃n∈ω，f:n→A) 覆盖目标中的全部字母表。
  let φ : Formula 1 1 := .forallE (.existsE (.forallE (.iff (.mem .newest (.bound 1))
    (Formula.existsMem (.bound 3) (fn0_m .newest (.bound 3) (.bound 1))))))
  have read Z (hZ : M.TransitiveSet Z) (hωZ : M.mem ω Z) (hz : Nonempty {x // M.mem x Z}) :
      Formula.satisfies (⟨fun _ => ⟨ω, hωZ⟩, fun _ => ⟨ω, hωZ⟩⟩ : Env (rt_model_l Z hz) 1) φ ↔
        ∀ A, M.mem A Z → ∃ K, M.mem K Z ∧ ∀ f, M.mem f Z →
          (M.mem f K ↔ ∃ n, M.mem n ω ∧ Fn0_d n A f) := by
    have fn (ρ : Env (rt_model_l Z hz) 5) : Formula.satisfies ρ (fn0_m .newest (.bound 3) (.bound 1)) ↔
        Fn0_d (ρ.bound 0).val (ρ.bound 3).val (ρ.bound 1).val :=
      (rt_model_delta_l hZ hz (fn0_delta_l ..) ρ).trans (fn0_sat_l hZF.1 ..)
    simp only [φ, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, Formula.satisfies_existsMem_iff, fn]
    constructor
    · intro h A hA
      obtain ⟨K, hK⟩ := h ⟨A, hA⟩
      exact ⟨K.val, K.property, fun f hf => (hK ⟨f, hf⟩).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩⟩⟩
    · intro h A
      obtain ⟨K, hK, spec⟩ := h A.val A.property
      exact ⟨⟨K, hK⟩, fun f => (spec f.val f.property).trans
        ⟨fun ⟨n, hn, hf⟩ => ⟨⟨n, hZ ω hωZ n hn⟩, hn, hf⟩, fun ⟨n, hn, hf⟩ => ⟨n.val, hn, hf⟩⟩⟩
  let nz : Nonempty {x // M.mem x X} := ⟨⟨ω, hωX⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, hωY⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have transfer := spred_source_l I hZF hω ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hq⟩ nz ny φ
    (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed])
    ⟨fun _ => ⟨ω, hωX⟩, fun _ => ⟨ω, hωX⟩⟩ ⟨fun _ => ⟨ω, hωY⟩, fun _ => ⟨ω, hωY⟩⟩ (fun _ => hωq)
  have target := (read Y hY hωY ny).mp (transfer.mp ((read X hX hωX nz).mpr (fun A hA => by
    obtain ⟨K, hK, spec⟩ := source A hA
    exact ⟨K, hK, fun f _ => (spec f).trans (exists_congr fun n => and_congr_right fun _ =>
      ⟨fn0_of_function_l (ZF.modelsKP hZF), fn0_function_l (ZF.modelsKP hZF)⟩)⟩)))
  intro A hA
  obtain ⟨K, hK, spec⟩ := target A hA
  -- 内部归纳保证每张背景有限函数图都在目标中，故相对空间就是完整空间。
  refine ⟨K, hK, fun f => ⟨?_, ?_⟩⟩
  · intro hf
    obtain ⟨n, hn, hf⟩ := (spec f (hY K hK f hf)).mp hf
    exact ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hf⟩
  · rintro ⟨n, hnω, hf⟩
    have fn := fn0_of_function_l (ZF.modelsKP hZF) hf
    exact (spec f (sc_finite_function_l hZF hω hY hn theory hωY hA hnω fn)).mpr ⟨n, hnω, fn⟩

end YesMetaZFC.SetTheory.Internal
