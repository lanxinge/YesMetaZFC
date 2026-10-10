import YesMetaZFC.SetTheory.FinitaryClub
import YesMetaZFC.SetTheory.Card.FiniteSequenceEnd

/-! # 以有限参数末项索引的运算切片

将阶段编号作为参数列的最后一项；一个共同有限元运算的闭集，自动对属于
该闭集的每个阶段切片闭合。切片是实际集合函数图，构造只需要 ZF。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Fc_slice_d (ω G i k x : M.Domain) : Prop := ∃ l f F k',
  I.Codes k l f ∧ Fseq_end_d I ω F f i ∧ I.Codes k' l F ∧ M.PairMember I k' x G

def fc_slice_m {d} (ω G i k x : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (𝒞.code k.weaken.weaken.weaken.weaken (.bound 3) (.bound 2))
    (.conj (fseq_end_m (𝒞 := 𝒞) ω.weaken.weaken.weaken.weaken (.bound 1) (.bound 2) i.weaken.weaken.weaken.weaken)
    (.conj (𝒞.code .newest (.bound 3) (.bound 1))
      (Formula.orderedPairMem 𝒞 .newest x.weaken.weaken.weaken.weaken G.weaken.weaken.weaken.weaken)))))))
derive_free_closed fc_slice_m

theorem fc_slice_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω G i k x : Term d) :
    Formula.satisfies ρ (fc_slice_m (𝒞 := 𝒞) ω G i k x) ↔
      Fc_slice_d I (ω.eval ρ) (G.eval ρ) (i.eval ρ) (k.eval ρ) (x.eval ρ) := by
  simp only [fc_slice_m, Fc_slice_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, fseq_end_sat_l I hE, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  rfl

/-- 共同运算 G 在阶段 i 上的实际切片，同时保持所有含 i 的闭集。 -/
theorem ZF.fc_slice_l (hZF : M.Models ZF) {ω X S T D G i} (hω : M.IsOmega ω)
    (hS : Fseq_space_d I ω X S) (hD : M.IsCartesianProduct I D T S)
    (hG : M.IsSetFunctionFromTo I G D X) (hi : M.mem i X) : ∃ K,
    M.IsSetFunctionFromTo I K D X ∧
    (∀ k x, M.PairMember I k x K ↔ M.mem k D ∧ Fc_slice_d I ω G i k x) ∧
    ∀ N, M.mem i N → Fc_closed_d I ω T G N → Fc_closed_d I ω T K N := by
  let ρ : Env M 3 := ((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push G).push i
  let φ : BinarySchema 3 := { body := fc_slice_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  have hφ k x : φ.denote ρ k x ↔ Fc_slice_d I ω G i k x := fc_slice_sat_l I hZF.1 _ _ _ _ _ _
  have total k (hk : M.mem k D) : ∃ x, φ.denote ρ k x := by
    obtain ⟨l, hl, f, hf, hlf⟩ := (hD k).mp hk
    obtain ⟨n, hn, hf⟩ := (hS f).mp hf
    obtain ⟨m, F, hm, hF, hEnd⟩ := ZF.fseq_end_exists_l I hZF hω hn hf hi
    obtain ⟨k', hk'⟩ := I.total l F
    obtain ⟨x, _, hx⟩ := hG.2.2 k' ((hD k').mpr ⟨l, hl, F, (hS F).mpr ⟨m, hm, hF⟩, hk'⟩)
    exact ⟨x, (hφ k x).mpr ⟨l, f, F, k', hlf, hEnd, hk', hx⟩⟩
  have unique k (_ : M.mem k D) x y (hx : φ.denote ρ k x) (hy : φ.denote ρ k y) : x = y := by
    obtain ⟨l, f, F, k', hk, hF, hk', hx⟩ := (hφ k x).mp hx
    obtain ⟨l', f', F', k'', hk'', hF', hpair, hy⟩ := (hφ k y).mp hy
    obtain ⟨rfl, rfl⟩ := I.injective hk hk''
    have hFF := fseq_end_rebuild_l I hZF.1 hF hF'
    subst F'
    have hkk := I.unique hk' hpair
    subst k''
    exact hG.1.2 k' x y hx hy
  obtain ⟨K, hK, hK'⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun k x _ hx => by
      obtain ⟨_, _, _, k', _, _, _, hx⟩ := (hφ k x).mp hx
      exact hG.output_mem_of_pairMember hx)
  have edge k x : M.PairMember I k x K ↔ M.mem k D ∧ Fc_slice_d I ω G i k x :=
    (hK' k x).trans (and_congr_right fun _ => hφ k x)
  refine ⟨K, hK, edge, fun N hiN hN x hx => ?_⟩
  obtain ⟨n, f, l, k, hn, hf, hl, hk, hx⟩ := hx
  obtain ⟨l', f', F, k', hk', hEnd, hpair, hx⟩ := ((edge k x).mp hx).2
  obtain ⟨rfl, rfl⟩ := I.injective hk hk'
  obtain ⟨m, F', hm, hF', hEnd'⟩ := ZF.fseq_end_exists_l I hZF hω hn hf hiN
  have hFF := fseq_end_rebuild_l I hZF.1 hEnd hEnd'
  subst F'
  exact hN x ⟨m, F, l, k', hm, hF', hl, hpair, hx⟩

end YesMetaZFC.SetTheory
