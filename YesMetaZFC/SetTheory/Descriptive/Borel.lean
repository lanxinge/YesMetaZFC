import YesMetaZFC.SetTheory.Descriptive.Borel.Open

/-! # 内部 Borel 集及空间实例

合法码是内部良基的带标签前缀树，求值及码的补、内部可数并均已实际构造。
`Borel_d` 表示有内部码的集合；可数并接口的输入是内部码族，在 ZF 中不擅自
从逐项有码推断可以同时选择一族码。地址长度、良基性和求值全部留在原模型中。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 所有有码子集组成实际内部集合，不把 Borel 性只留作外部类谓词。 -/
theorem borel_collection_l (hZF : M.Models ZF) (ω A S B : M.Domain) :
    ∃ C, ∀ K, M.mem K C ↔ Borel_d I ω A S B K := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push S).push B
  let φ : UnarySchema 4 := { body := borel_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨C, fun K => ((hC K).trans (and_congr_right fun _ => borel_sat_l I hZF.1 _ _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨c, _, hk⟩ := h
  exact (hP K).mpr (fun x hx => ((hk x).mp hx).1)

/-- 同一码限制到内部子空间，解释恰为原解释与子空间的交。 -/
theorem borel_restrict_l (hZF : M.Models ZF) {ω A S B D K} (hD : M.MemberSubset D B)
    (hK : Borel_d I ω A S B K) :
    ∃ L, Borel_d I ω A S D L ∧ ∀ x, M.mem x L ↔ M.mem x D ∧ M.mem x K := by
  obtain ⟨c, hc, hK⟩ := hK
  obtain ⟨L, hL, _⟩ := bden_exists_unique_l I hZF ω A S D c
  exact ⟨L, ⟨c, hc, hL⟩, fun x => (hL x).trans (and_congr_right fun hx =>
    ((hK x).trans ⟨And.right, fun h => ⟨hD x hx, h⟩⟩).symm)⟩

/-- 一次给出 Baire、Cantor 的实际空间、前缀空间和开集／闭树体的有码性。 -/
theorem baire_cantor_borel_l (hZF : M.Models ZF) : ∃ ω D B C A S,
    Baire_d I ω B ∧ Cantor_d I ω C ∧ Fseq_space_d I ω ω A ∧ Fseq_space_d I ω D S ∧
    (∀ U, Open_d A B U → Borel_d I ω A A B U) ∧
    (∀ U, Open_d S C U → Borel_d I ω A S C U) ∧
    (∀ T, ∃ K, Body_d A B T K ∧ Borel_d I ω A A B K) ∧
    (∀ T, ∃ K, Body_d S C T K ∧ Borel_d I ω A S C K) := by
  obtain ⟨ω, D, B, C, A, S, hB, hD, hC, hA, ha, hS, hs⟩ := ds_spaces_l I hZF
  have body {P Y} (hp : M.CardinalLessOrEqual I P ω) (T : M.Domain) :
      ∃ K, Body_d P Y T K ∧ Borel_d I ω A P Y K := by
    obtain ⟨K, hK⟩ := tree_body_exists_l (ZF.modelsKP hZF) P Y T
    exact ⟨K, hK, tree_body_borel_l I hZF hB.1 hA hp hK⟩
  exact ⟨ω, D, B, C, A, S, hB, ⟨hB.1, D, hD, hC⟩, hA, hS,
    fun _ h => bcode_open_l I hZF hB.1 hA ha h, fun _ h => bcode_open_l I hZF hB.1 hA hs h,
    body ha, body hs⟩

end YesMetaZFC.SetTheory.Descriptive
