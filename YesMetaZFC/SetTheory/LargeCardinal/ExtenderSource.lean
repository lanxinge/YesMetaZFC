import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctions
import YesMetaZFC.Model.SetTheory.Internal.SourceReindex
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant
import YesMetaZFC.Model.SetTheory.Internal.SourceSequences
import YesMetaZFC.Model.SetTheory.Internal.SourceCollapse
import YesMetaZFC.SetTheory.HereditaryCover
import YesMetaZFC.SetTheory.HereditarySequences

/-! # 有限支撑系统的实际源数据

分离与集合代数适用于任意源内集合；统一化与塌缩只作用于源内小集合。这些性质
沿完整初等嵌入传递到后继模型。全部函数空间、投影与代表拉回由此构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Ep_source_d (hZF : M.Models ZF) (ω κ K X R : M.Domain) : Prop where
  omega : M.IsOmega ω
  below : M.MemberSubset ω κ
  transitive : M.TransitiveSet X
  omega_mem : M.mem ω X
  cardinal_mem : M.mem κ X
  cardinal_small : Sc_small_d X κ
  finite_mem : M.mem K X
  finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K
  code : ∃ c, Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R
  theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R
  collection : Sc_collection_d (kp_pair_l (ZF.modelsKP hZF)) ω X R
  sequences : Sc_sequences_d (kp_pair_l (ZF.modelsKP hZF)) ω X
  collapse : Sc_collapse_d X

/-- 新字母表的小性由源内实际单射给出。 -/
theorem Ep_source_d.rebase_l (hZF : M.Models ZF) {ω κ K X R μ : M.Domain} (h : Ep_source_d hZF ω κ K X R)
    (hμ : M.mem μ X) (hωμ : M.MemberSubset ω μ) (small : Sc_small_d X μ) : ∃ K', Ep_source_d hZF ω μ K' X R := by
  obtain ⟨K', hk, hs⟩ := h.sequences.space μ hμ
  exact ⟨K', h.omega, hωμ, h.transitive, h.omega_mem, hμ, small, hk, hs, h.code, h.theory, h.collection, h.sequences, h.collapse⟩

theorem Ep_source_d.space_l (hZF : M.Models ZF) {ω κ K X R n : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) : ∃ D, M.mem D X ∧ Ep_space_d κ n D := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, hm⟩ := h.code
  let φ : Delta0UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest, delta0 := fn0_delta_l .. }
  let ρ : Env M 2 := (⟨fun _ => n, fun _ => n⟩ : Env M 1).push κ
  obtain ⟨D, hDX, hd⟩ := sc_separate_source_l I hZF h.omega h.transitive hm h.theory
    φ.toUnarySchema φ.delta0 ρ (Fin.cases h.cardinal_mem (fun _ => h.transitive ω h.omega_mem n hn)) h.finite_mem
  refine ⟨D, hDX, fun s => (hd s).trans ?_⟩
  have sat : φ.toUnarySchema.denote ρ s ↔ Fn0_d n κ s := fn0_sat_l hZF.1 _ _ _ _
  exact (and_congr_right fun _ => sat).trans ⟨And.right, fun hs =>
    ⟨(h.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs⟩, hs⟩⟩

theorem Ep_source_d.space_mem_l (hZF : M.Models ZF) {ω κ K X R n D : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) : M.mem D X := by
  obtain ⟨E, he, hs⟩ := h.space_l hZF hn
  exact hZF.1.eq_of_same_members E D (fun s => (hs s).trans (hD s).symm) ▸ he

theorem Ep_source_d.uniform_l (hZF : M.Models ZF) {ω κ K X R n D : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) :
    Sc_uniform_d (kp_pair_l (ZF.modelsKP hZF)) ω X R D := by
  obtain ⟨c, hc⟩ := h.code
  exact h.collection D (h.space_mem_l hZF hn hD)
    ((h.sequences.small_l hZF h.omega h.transitive hc h.theory h.omega_mem h.cardinal_mem h.finite_mem h.finite h.cardinal_small).mono_l
      (fun s hs => (h.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hD s).mp hs)⟩))

theorem Ep_source_d.function_l (hZF : M.Models ZF) {ω κ K X R D f : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hf : M.mem f X)
    (hF : Fn0_d D X f) : Sfun_d X D f := sc_function_domain_l h.theory.algebra hf hF

theorem Ep_source_d.projection_l (hZF : M.Models ZF) {ω κ K X R m n q D E : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  obtain ⟨c, hM⟩ := h.code
  have hqX := h.transitive K h.finite_mem q ((h.finite q).mpr ⟨m, hm,
    fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l fun i hi => h.below i (h.omega.transitive hZF n hn i hi))⟩)
  exact sc_reindex_l hZF h.omega h.transitive hM h.theory
    (h.transitive ω h.omega_mem m hm) (h.transitive ω h.omega_mem n hn) h.cardinal_mem hqX
    (h.space_mem_l hZF hn hE) hq hD hE

theorem Ep_source_d.family_l (hZF : M.Models ZF) {ω κ K X R m n q D E F G : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (hF : ∀ f, M.mem f F ↔ M.mem f X ∧ Fn0_d D X f) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d E X g) :
    ∃ t P, M.mem t X ∧ Fn0_d E D t ∧
      (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP hZF)) P F G ∧
      ∀ f g, Rd_entry_d f g P ↔ M.mem f F ∧ M.mem g G ∧ Cp0_d E D X t f g := by
  obtain ⟨t, htX, ht, spec⟩ := h.projection_l hZF hm hn hq hD hE
  obtain ⟨c, hM⟩ := h.code
  obtain ⟨P, hp, hs⟩ := rs_pullback_family_l hZF h.omega h.transitive hM h.theory
    (h.space_mem_l hZF hn hE) (h.space_mem_l hZF hm hD) htX ht hF hG
  exact ⟨t, P, htX, ht, spec, hp, hs⟩

theorem Ep_source_d.model_l (hZF : M.Models ZF) {ω κ K X R n D U : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω)
    (hD : Ep_space_d κ n D) (hU : FilterZF.Base_d (ℳ := M) D U) (S : M.Domain) : ∃ G c p C T,
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧
      Rp_model_d (kp_pair_l (ZF.modelsKP hZF)) D X U S c G p C T := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨c, hM⟩ := h.code
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := sc_constant_l hZF h.omega h.transitive hM h.theory
    (h.space_mem_l hZF hn hD) h.cardinal_mem
  exact rp_family_model_l I hZF hU hfX (hf.mono_target_l (h.transitive A hAX)) S

/-- 正则 Hχ 给出初始源理论及全部字母表的实际有限序列空间。 -/
theorem ep_source_of_h_l (hZFC : M.Models ZFC) {ω κ K χ X : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) (hωX : M.mem ω X) (hκX : M.mem κ X)
    (hKX : M.mem K X) (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω κ K) :
    ∃ R, Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.h_transitive_l I hZF hX
  obtain ⟨c, R, hc, hr⟩ := smdl_membership_l I hZF ⟨κ, hκX⟩
  exact ⟨R, hω, hωκ, ht, hωX, hκX, sc_h_small_l hZFC hω hχ hωχ hX hκX, hKX, hK, ⟨c, hc, hr⟩,
    sc_h_theory_l hZFC hω hχ hωχ hX R, sc_h_collection_l hZFC hω hχ hωχ hX R,
    sc_h_sequences_l hZFC hω hχ hωχ hX, sc_h_collapse_l hZFC hω hχ hωχ hX⟩

/-- 传递初等后继在任意源内小参数 κ′ 上重新成为源；无需 κ′ 在旧嵌入的像中。 -/
theorem Ep_source_d.successor_l (hZF : M.Models ZF) {ω κ K X R c d N W j κ' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R)
    (hm : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (hn : Smem_d (kp_pair_l (ZF.modelsKP hZF)) d N W) (hN : M.TransitiveSet N)
    (hj : Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X N j)
    (hκ : M.mem κ' N) (hωκ : M.MemberSubset ω κ') (small : Sc_small_d N κ') : ∃ K', Ep_source_d hZF ω κ' K' N W := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have theory := source.theory.map_l I hZF source.omega source.transitive hN hm hn hj
  have seq := (sc_sequences_iff_l hZF source.omega source.transitive hN hm hn hj
    source.omega_mem source.theory theory).mp source.sequences
  obtain ⟨K', hK, hs⟩ := seq.space κ' hκ
  have hωN := hj.1.1.output_mem_of_pairMember (hj.omega_l I hZF source.omega source.transitive hN hm hn source.omega_mem)
  exact ⟨K', source.omega, hωκ, hN, hωN, hκ, small, hK, hs, ⟨d, hn⟩, theory,
    source.collection.map_l _ hZF source.omega source.transitive hN hm hn hj, seq,
    (sc_collapse_iff_l hZF source.omega source.transitive hN hm hn hj).mp source.collapse⟩

/-- 自动覆盖指定参数，并包含有限 κ 幂的全部子集；可分别用作所属模型与施加源。 -/
theorem ep_source_exists_l (hZFC : M.Models ZFC) (A : M.Domain) {ω κ : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ) :
    ∃ K X R, Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R ∧ M.mem A X ∧
      ∀ n D B, M.mem n ω → Ep_space_d κ n D → M.MemberSubset B D → M.mem B X := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) κ K
  obtain ⟨B, hB⟩ := KP.exists_pair (ZF.modelsKP hZF) ω A
  obtain ⟨Q, hQ⟩ := KP.exists_pair (ZF.modelsKP hZF) B P
  obtain ⟨χ, X, hχ, hωχ, hX, hQX⟩ := ZFC.h_cover_l I hZFC hω Q
  have ht := ZF.h_transitive_l I hZF hX
  have hBX := ht Q hQX B ((hQ B).mpr (Or.inl rfl))
  have hPX := ht Q hQX P ((hQ P).mpr (Or.inr rfl))
  have hKX := ht P hPX K ((hP K).mpr (Or.inr rfl))
  obtain ⟨R, hR⟩ := ep_source_of_h_l hZFC hω hωκ hχ hωχ hX
    (ht B hBX ω ((hB ω).mpr (Or.inl rfl))) (ht P hPX κ ((hP κ).mpr (Or.inl rfl))) hKX hK
  exact ⟨K, X, R, hR, ht B hBX A ((hB A).mpr (Or.inr rfl)), fun n D B hn hD hBD =>
    ZF.h_subsets_l I hZF hχ.isLimitOrdinal hX hKX B fun s hs =>
      (hK s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((hD s).mp (hBD s hs))⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
