import YesMetaZFC.SetTheory.LargeCardinal.ExtenderReadSource
import YesMetaZFC.Model.SetTheory.Internal.TypeTruthSyntax
import YesMetaZFC.Model.SetTheory.Internal.TransitiveRecursion
import YesMetaZFC.Model.SetTheory.Internal.TypeNamesSource

/-! # 有限闭源中的完整查询域

所有背景有限函数由已经实现的有限闭性回收。名字域和序列空间保留原见证，
不把源内量词误读成背景中的全部集合，也不要求源满足 KP。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {ω X : M.Domain} (source : Fs_read_d ω X)
  (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l (Fs_read_d.transitive source) nx (And.left hKP) (Fs_read_d.pair source)
include source

theorem Fs_read_d.fseq_read_l (w A E : (N).Domain) (hw : w.val = ω) :
    Fseq_space_d J w A E ↔ Fseq_space_d I ω A.val E.val := by
  have fn (f n : (N).Domain) := rt_function_from_l source.transitive nx hKP.1
    (KP.exists_pair hKP) source.pair f n A
  constructor
  · intro seq f
    constructor
    · intro hf
      obtain ⟨n, hn, ff⟩ := (seq ⟨f, source.transitive E.val E.property f hf⟩).mp hf
      exact ⟨n.val, hw ▸ hn, (fn _ n).mp ff⟩
    · rintro ⟨n, hn, ff⟩
      let n₀ : (N).Domain := ⟨n, source.transitive ω source.omega_mem n hn⟩
      let f₀ : (N).Domain := ⟨f, source.functions n A.val f hn
        (source.transitive A.val A.property) (fn0_of_function_l hKP ff)⟩
      have hnw : (N).mem n₀ w := by
        change M.mem n w.val
        exact hw.symm ▸ hn
      exact (seq f₀).mpr ⟨n₀, hnw, (fn f₀ n₀).mpr ff⟩
  · intro seq f
    refine (seq f.val).trans ⟨fun ⟨n, hn, ff⟩ => ?_, fun ⟨n, hn, ff⟩ => ⟨n.val, hw ▸ hn, (fn f n).mp ff⟩⟩
    exact ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw.symm ▸ hn, (fn f _).mpr ff⟩

theorem Fs_read_d.pool_sat_l {d} (ρ : Env N d) (o n U D : Term d) (hw : (o.eval ρ).val = ω) :
    Formula.satisfies ρ (tt_pool_m o n U D) ↔
      ∃ A E, M.mem A X ∧ M.mem E X ∧ Tn_names_d (n.eval ρ).val (U.eval ρ).val A ∧
        Fseq_space_d I ω A E ∧ M.IsCartesianProduct I (D.eval ρ).val ω E := by
  have read (A E : (N).Domain) :
      Formula.satisfies ((ρ.push A).push E)
        (.conj (tn_names0_m n.weaken.weaken U.weaken.weaken Term.newest.weaken)
          (.conj (fseq_space_m (𝒞 := kpair_convention_l) o.weaken.weaken Term.newest.weaken .newest)
            (Formula.isCartesianProduct kpair_convention_l D.weaken.weaken o.weaken.weaken .newest))) ↔
      Tn_names_d (n.eval ρ).val (U.eval ρ).val A.val ∧ Fseq_space_d I ω A.val E.val ∧
        M.IsCartesianProduct I (D.eval ρ).val ω E.val := by
    have names := (rt_model_delta_l source.transitive nx (tn_names0_delta_l ..) ((ρ.push A).push E)).trans
      (tn_names0_sat_l hKP _ n.weaken.weaken U.weaken.weaken Term.newest.weaken)
    simp only [@eval_image_env_l N M Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at names
    simp only [Formula.satisfies_conj_iff, names, fseq_space_sat_l J (rt_model_ext_l hKP.1 source.transitive nx),
      Formula.satisfies_isCartesianProduct_iff J, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
    exact and_congr Iff.rfl (and_congr (source.fseq_read_l hKP nx _ A E hw)
      (by simpa only [hw, kp_pair_l] using rt_cartesian_l hKP.1 (KP.exists_pair hKP) source.transitive nx source.pair (D.eval ρ) (o.eval ρ) E))
  simp only [tt_pool_m, Formula.satisfies_exists_iff, read]
  exact ⟨fun ⟨A, E, h⟩ => ⟨A.val, E.val, A.property, E.property, h⟩,
    fun ⟨A, E, hA, hE, h⟩ => ⟨⟨A, hA⟩, ⟨E, hE⟩, h⟩⟩

omit source in
/-- 相对极限秩段自动回收完整查询域及其两份原见证。 -/
theorem Ep_source_d.pool_rank_l (hZF : M.Models ZF) {ω κ K Z R α V n U D : M.Domain}
    (source : Ep_source_d hZF ω κ K Z R) (hV : M.mem V Z) (rank : Vr_d Z α V)
    (hα : M.IsLimitOrdinal α) (hw : M.mem ω V) (hn : M.mem n V) (hU : M.mem U V)
    (pool : Tt_pool_d (kp_pair_l (ZF.modelsKP hZF)) ω n U D) :
    M.mem D V ∧ ∃ A E, M.mem A V ∧ M.mem E V ∧ Tn_names_d n U A ∧
      Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) ω A E ∧
      M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) D ω E := by
  let P := kp_pair_l (ZF.modelsKP hZF)
  have ht := rank.transitive_l hZF source.transitive hV
  obtain ⟨c, S, model⟩ := smdl_membership_l P hZF ⟨ω, hw⟩
  have theory := source.rank_theory_l hZF hV rank hα model
  obtain ⟨A, hA, names⟩ := tn_names_source_l hZF source.omega ht model theory hn hU
  obtain ⟨E, hE, seq⟩ := (source.rank_sequences_l hZF hV rank hα hw).space A hA
  obtain ⟨D₀, hD₀, product⟩ := theory.algebra.product ω E hw hE
  obtain ⟨A', E', names', seq', product'⟩ := pool
  have eqA := hZF.1.eq_of_same_members A' A (fun x => (names' x).trans (names x).symm)
  subst A'
  have eqE := hZF.1.eq_of_same_members E' E (fun f => (seq' f).trans (seq f).symm)
  subst E'
  have eqD := hZF.1.eq_of_same_members D₀ D (fun p => (product p).trans (product' p).symm)
  exact ⟨eqD ▸ hD₀, A, E, hA, hE, names, seq, product'⟩

end YesMetaZFC.SetTheory.LargeCardinal
