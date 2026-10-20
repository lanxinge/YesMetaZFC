import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadRelative
import YesMetaZFC.Model.SetTheory.Internal.ZfcTransfer

/-! # 给定地模型的实际扩展器源初值

有限序列空间由原模型的 ZF 构造，全部背景内部有限图由有限读写闭包回收。
小关系的坍塌在原模型内部实施。两者均不要求原模型对外部 ω 列封闭。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (ground : (rt_model_l X nx).Models ZF)
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "J" => kp_pair_l (ZF.modelsKP ground)
include hZF hX ground

theorem fs_sequences_relative_l (ω : (N).Domain) (hω : M.IsOmega ω.val) : Sc_sequences_d I ω.val X := by
  have fs := fs_read_relative_l hZF hX nx ground ω hω
  have hw := rt_omega_l hX nx hZF.1 ω hω
  have decode (A K : (N).Domain) (seq : Fseq_space_d J ω A K) : Fseq_space_d I ω.val A.val K.val := by
    intro f
    constructor
    · intro hf
      let g : (N).Domain := ⟨f, hX K.val K.property f hf⟩
      obtain ⟨n, hn, fn⟩ := (seq g).mp hf
      exact ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
        ((rt_fn_l hX nx hZF.1 n A g).mp (fn0_of_function_l (ZF.modelsKP ground) fn))⟩
    · rintro ⟨n, hn, fn⟩
      let m : (N).Domain := ⟨n, hX ω.val ω.property n hn⟩
      let g : (N).Domain := ⟨f, fs.functions n A.val f hn (hX A.val A.property)
        (fn0_of_function_l (ZF.modelsKP hZF) fn)⟩
      exact (seq g).mpr ⟨m, hn, fn0_function_l (ZF.modelsKP ground)
        ((rt_fn_l hX nx hZF.1 m A g).mpr (fn0_of_function_l (ZF.modelsKP hZF) fn))⟩
  have encode (A K : (N).Domain) (seq : Fseq_space_d I ω.val A.val K.val) : Fseq_space_d J ω A K := by
    intro f
    constructor
    · intro hf
      obtain ⟨n, hn, fn⟩ := (seq f.val).mp hf
      let m : (N).Domain := ⟨n, hX ω.val ω.property n hn⟩
      exact ⟨m, hn, fn0_function_l (ZF.modelsKP ground)
        ((rt_fn_l hX nx hZF.1 m A f).mpr (fn0_of_function_l (ZF.modelsKP hZF) fn))⟩
    · rintro ⟨n, hn, fn⟩
      exact (seq f.val).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF)
        ((rt_fn_l hX nx hZF.1 n A f).mp (fn0_of_function_l (ZF.modelsKP ground) fn))⟩
  refine ⟨?_, ?_⟩
  · intro A hA
    obtain ⟨K, seq⟩ := ZF.fseq_space_exists_l J ground hw ⟨A, hA⟩
    exact ⟨K.val, K.property, decode ⟨A, hA⟩ K seq⟩
  · intro A K μ e hA hK hμ he seq above idx
    let ρ : Env N 3 := ⟨Fin.cases ω (Fin.cases ⟨A, hA⟩ (fun _ => ⟨K, hK⟩)), fun _ => ω⟩
    apply (sc_seq_index_sat_l (ZF.modelsKP hZF) hX nx ρ .newest (.bound 1) (.bound 2)).mp ?_ μ e hμ he above idx
    simp only [sc_seq_index_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_subset_iff, sc_index_sat_l (ZF.modelsKP ground),
      Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    intro ν q bound index
    obtain ⟨f, fn⟩ := ZF.fseq_ordinal_bound_l J ground hw index.ordinal bound
      (index.bound_l (ZF.modelsKP ground)) (encode ⟨A, hA⟩ ⟨K, hK⟩ seq)
    exact ⟨f, Sc_index_d.of_injection_l (ZF.modelsKP ground) index.ordinal fn⟩

theorem fs_collapse_relative_l : Sc_collapse_d X := by
  obtain ⟨x, hx⟩ : ∃ x, M.mem x X := nx.elim (fun x => ⟨x.val, x.property⟩)
  let ρ : Env N 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  apply (sc_collapse_sat_l (ZF.modelsKP hZF) hX nx ρ).mp
  simp only [sc_collapse_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, wf_rel_sat_l ground.1, wc_ext_sat_l ground.1,
    wc_iso_sat_l ground.1]
  exact fun _ _ _ wf ext => wc_iso_exists_l ground wf ext

end YesMetaZFC.SetTheory.LargeCardinal

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel LargeCardinal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 给定模型的同一个载体和关系给出完整源；没有重新选择较强工作根。 -/
theorem Zc_model_d.source_l {ω c X R κ : M.Domain} (hω : M.IsOmega ω) (hX : M.TransitiveSet X)
    (hm : Smem_d I c X R) (h : Zc_model_d I ω c X R) (hwX : M.mem ω X)
    (hκ : M.mem κ X) (ord : M.IsOrdinal κ) (above : M.MemberSubset ω κ) : ∃ K, Ep_source_d hZF ω κ K X R := by
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hwX⟩⟩
  have ground := ZFC.models_zf_l (h.membership_l I hZF hω hm nx)
  have seq := fs_sequences_relative_l hZF hX nx ground ⟨ω, hwX⟩ hω
  have theory := h.theory_l hZF hω hX hm
  obtain ⟨K, hk, space⟩ := seq.space κ hκ
  exact ⟨K, hω, above, hX, hwX, hκ, sc_ordinal_small_l hZF hω hX hm theory hκ ord,
    hk, space, ⟨c, hm⟩, theory, h.collection_l hZF hω hX hm, seq, fs_collapse_relative_l hZF hX nx ground⟩

end YesMetaZFC.SetTheory.Internal
