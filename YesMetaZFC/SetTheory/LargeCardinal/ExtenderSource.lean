import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFunctions
import YesMetaZFC.Model.SetTheory.Internal.SourceReindex
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Constant
import YesMetaZFC.Model.SetTheory.Internal.Isomorphism
import YesMetaZFC.SetTheory.HereditaryCover

/-! # 有限支撑系统的实际源数据

只打包既有 H(χ) 初等嵌入与源中参数，不引入闭包操作提供器。
全部有限函数空间、坐标投影及源代表的拉回均在下面实际构造。
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
  finite_mem : M.mem K X
  finite : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K
  presentation : ∃ χ c d H S e, M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) χ ∧ M.mem ω χ ∧
    H_d (kp_pair_l (ZF.modelsKP hZF)) χ H ∧ Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R ∧
    Smem_d (kp_pair_l (ZF.modelsKP hZF)) d H S ∧ Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X H e

theorem Ep_source_d.space_l (hZF : M.Models ZF) {ω κ K X R n : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) : ∃ D, M.mem D X ∧ Ep_space_d κ n D := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hm, ht, he⟩ := h.presentation
  let φ : Delta0UnarySchema 2 := { body := fn0_m (.bound 2) (.bound 1) .newest, delta0 := fn0_delta_l .. }
  let ρ : Env M 2 := (⟨fun _ => n, fun _ => n⟩ : Env M 1).push κ
  obtain ⟨D, hDX, hd⟩ := smap_separate_source_l I hZF h.omega hχ.isLimitOrdinal hH h.transitive hm ht he
    φ.toUnarySchema φ.delta0 ρ (Fin.cases h.cardinal_mem (fun _ => h.transitive ω h.omega_mem n hn)) h.finite_mem
  refine ⟨D, hDX, fun s => (hd s).trans ?_⟩
  have sat : φ.toUnarySchema.denote ρ s ↔ Fn0_d n κ s := fn0_sat_l hZF.1 _ _ _ _
  exact (and_congr_right fun _ => sat).trans ⟨And.right, fun hs =>
    ⟨(h.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs⟩, hs⟩⟩

theorem Ep_source_d.space_mem_l (hZF : M.Models ZF) {ω κ K X R n D : M.Domain}
    (h : Ep_source_d hZF ω κ K X R) (hn : M.mem n ω) (hD : Ep_space_d κ n D) : M.mem D X := by
  obtain ⟨E, he, hs⟩ := h.space_l hZF hn
  exact hZF.1.eq_of_same_members E D (fun s => (hs s).trans (hD s).symm) ▸ he

theorem Ep_source_d.function_l (hZFC : M.Models ZFC) {ω κ K X R D f : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hD : M.mem D X) (hf : M.mem f X)
    (hF : Fn0_d D X f) : Sfun_d X D f := by
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hm, hn, he⟩ := h.presentation
  exact smap_function_domain_l hZFC h.omega hχ hωχ hH h.transitive hm hn he hD hf hF

theorem Ep_source_d.projection_l (hZFC : M.Models ZFC) {ω κ K X R m n q D E : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E) :
    ∃ t, M.mem t X ∧ Fn0_d E D t ∧ ∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hM, hN, he⟩ := h.presentation
  have hqX := h.transitive K h.finite_mem q ((h.finite q).mpr ⟨m, hm,
    fn0_function_l (ZF.modelsKP hZF) (hq.mono_target_l fun i hi => h.below i (h.omega.transitive hZF n hn i hi))⟩)
  exact smap_reindex_l hZFC h.omega hχ hωχ hH h.transitive hM hN he
    (h.transitive ω h.omega_mem m hm) (h.transitive ω h.omega_mem n hn) h.cardinal_mem hqX
    (h.space_mem_l hZF hn hE) hq hD hE

theorem Ep_source_d.family_l (hZFC : M.Models ZFC) {ω κ K X R m n q D E F G : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hm : M.mem m ω) (hn : M.mem n ω)
    (hq : Fn0_d m n q) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (hF : ∀ f, M.mem f F ↔ M.mem f X ∧ Fn0_d D X f) (hG : ∀ g, M.mem g G ↔ M.mem g X ∧ Fn0_d E X g) :
    ∃ t P, M.mem t X ∧ Fn0_d E D t ∧
      (∀ s r, Rd_entry_d s r t ↔ M.mem s E ∧ Cp0_d m n κ q s r) ∧
      M.IsSetFunctionFromTo (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) P F G ∧
      ∀ f g, Rd_entry_d f g P ↔ M.mem f F ∧ M.mem g G ∧ Cp0_d E D X t f g := by
  let hZF := ZFC.models_zf_l hZFC
  obtain ⟨t, htX, ht, spec⟩ := h.projection_l hZFC hm hn hq hD hE
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hM, hN, he⟩ := h.presentation
  obtain ⟨P, hp, hs⟩ := rs_pullback_family_l hZFC h.omega hχ hωχ hH h.transitive hM hN he
    (h.space_mem_l hZF hn hE) (h.space_mem_l hZF hm hD) htX ht hF hG
  exact ⟨t, P, htX, ht, spec, hp, hs⟩

theorem Ep_source_d.model_l (hZFC : M.Models ZFC) {ω κ K X R n D U : M.Domain}
    (h : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R) (hn : M.mem n ω)
    (hD : Ep_space_d κ n D) (hU : FilterZF.Base_d (ℳ := M) D U) : ∃ G c p C T,
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) ∧
      Rp_model_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) D X U R c G p C T := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨χ, c, d, H, S, e, hχ, hωχ, hH, hM, hN, he⟩ := h.presentation
  obtain ⟨f, A, hfX, hAX, hf, _⟩ := smap_constant_l hZFC h.omega hχ hωχ hH h.transitive hM hN he
    (h.space_mem_l hZF hn hD) h.cardinal_mem
  exact rp_family_model_l I hZF hU hfX (hf.mono_target_l (h.transitive A hAX)) R

/-- 给定实际正则 Hχ 和所需参数，以恒等图提供全部源证书。 -/
theorem ep_source_of_h_l (hZF : M.Models ZF) {ω κ K χ X : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP hZF)) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP hZF)) χ X) (hωX : M.mem ω X) (hκX : M.mem κ X)
    (hKX : M.mem K X) (hK : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K) :
    ∃ R, Ep_source_d hZF ω κ K X R := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  have ht := ZF.h_transitive_l I hZF hX
  obtain ⟨c, R, hc, hr⟩ := smdl_membership_l I hZF ⟨κ, hκX⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq (.bound 1) .newest }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => ω⟩
  have sat x y : φ.denote ρ x y ↔ x = y := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
  obtain ⟨e, he, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := X) (target := X)
    (fun x _ => ⟨x, (sat x x).mpr rfl⟩) (fun x _ y z hy hz => ((sat x y).mp hy).symm.trans ((sat x z).mp hz))
    (fun x y hx hy => (sat x y).mp hy ▸ hx)
  have eq x y (hxy : M.PairMember I x y e) := (sat x y).mp ((spec x y).mp hxy).2
  have bij : M.IsSetBijectionFromTo I e X X := ⟨⟨he, fun x y z hx hy => (eq x z hx).trans (eq y z hy).symm⟩,
    fun x hx => ⟨x, hx, (spec x x).mpr ⟨hx, (sat x x).mpr rfl⟩⟩⟩
  have elem := smap_of_iso_l I hZF hω hc hc bij (fun a b x y ha hb => eq a x ha ▸ eq b y hb ▸ Iff.rfl)
  exact ⟨R, hω, hωκ, ht, hωX, hκX, hKX, hK, χ, c, c, X, R, e, hχ, hωχ, hX, ⟨hc, hr⟩, ⟨hc, hr⟩, elem⟩

/-- 对任意 κ 实际构造包含其全部内部有限函数的源。 -/
theorem ep_source_exists_l (hZFC : M.Models ZFC) {ω κ : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ) :
    ∃ K X R, Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω κ
  obtain ⟨P, hP⟩ := KP.exists_pair (ZF.modelsKP hZF) κ K
  obtain ⟨Q, hQ⟩ := KP.exists_pair (ZF.modelsKP hZF) ω P
  obtain ⟨χ, X, hχ, hωχ, hX, hQX⟩ := ZFC.h_cover_l I hZFC hω Q
  have ht := ZF.h_transitive_l I hZF hX
  have hωX := ht Q hQX ω ((hQ ω).mpr (Or.inl rfl))
  have hPX := ht Q hQX P ((hQ P).mpr (Or.inr rfl))
  obtain ⟨R, hR⟩ := ep_source_of_h_l hZF hω hωκ hχ hωχ hX hωX
    (ht P hPX κ ((hP κ).mpr (Or.inl rfl))) (ht P hPX K ((hP K).mpr (Or.inr rfl))) hK
  exact ⟨K, X, R, hR⟩

end YesMetaZFC.SetTheory.LargeCardinal
