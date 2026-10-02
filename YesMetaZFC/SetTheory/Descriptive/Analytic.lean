import YesMetaZFC.SetTheory.Descriptive.Analytic.Diagonal
import YesMetaZFC.SetTheory.Descriptive.Analytic.NormalForm
import YesMetaZFC.SetTheory.Descriptive.Trace

/-! # 内部解析层入口

`An_d` 由 Borel 关系的 Baire 投影定义，`Coan_d` 为其相对补；`Aden_d` 有唯一
实际解释。已实现有码可数并、余解析补族的可数交、闭树投影及 Borel 集的解析
表示。`an_closed_l`、`an_tree_iff_l`、`an_prefix_iff_l` 给出闭集、闭树和逐内部
长度的正规形；`an_normal_l` 还返回规范无死节点树。解析类与任意内部子空间
上的迹都形成实际集合，全部定义有原公式。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem an_collection_l (hZF : M.Models ZF) (ω A B J : M.Domain) : ∃ C, ∀ K, M.mem K C ↔ An_d I ω A B J K := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF B
  let ρ : Env M 4 := (((⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push A).push B).push J
  let φ : UnarySchema 4 := { body := an_m (𝒞 := 𝒞) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ P
  refine ⟨C, fun K => ((hC K).trans (and_congr_right fun _ => an_sat_l I hZF.1 _ _ _ _ _ _)).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩⟩
  obtain ⟨_, _, R, _, hk⟩ := h
  exact (hP K).mpr (fun x hx => ((hk x).mp hx).1)

def Anrel_d (ω A B J X K : M.Domain) : Prop := ∃ L, An_d I ω A B J L ∧ Tr_d X L K
def anrel_m {d} (ω A B J X K : Term d) : Formula 1 d := .existsE (.conj
  (an_m (𝒞 := 𝒞) ω.weaken A.weaken B.weaken J.weaken .newest) (tr_m X.weaken .newest K.weaken))
derive_free_closed anrel_m
@[prove_auto_norm semantic]
theorem anrel_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B J X K : Term d) :
    Formula.satisfies ρ (anrel_m (𝒞 := 𝒞) ω A B J X K) ↔
      Anrel_d I (ω.eval ρ) (A.eval ρ) (B.eval ρ) (J.eval ρ) (X.eval ρ) (K.eval ρ) := by
  simp only [anrel_m, Anrel_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    an_sat_l I hE, tr_sat_l, Definitional.Term.eval_weaken]; rfl

theorem an_relative_l (hZF : M.Models ZF) (ω A B J X : M.Domain) :
    ∃ C, ∀ K, M.mem K C ↔ Anrel_d I ω A B J X K := by
  obtain ⟨S, hs⟩ := an_collection_l I hZF ω A B J
  obtain ⟨C, hc⟩ := rclass_collection_l hZF X S
  exact ⟨C, fun K => (hc K).trans (exists_congr fun L => and_congr_left fun _ => hs L)⟩

/-- 子空间相对化只改变自由实数的范围；见证仍取内部 Baire 实数。 -/
theorem anrel_prefix_iff_l (hZF : M.Models ZF) {ω A B J X K} (hB : Baire_d I ω B)
    (hA : Fseq_space_d I ω ω A) (ha : M.CardinalLessOrEqual I A ω) (hJ : Npair_d I ω J)
    (hX : M.MemberSubset X B) : Anrel_d I ω A B J X K ↔ ∃ T, Tree_d A T ∧ ∀ x,
      M.mem x K ↔ M.mem x X ∧ ∃ y, M.mem y B ∧ Tpath_d I ω J T x y := by
  constructor
  · rintro ⟨L, hl, hk⟩
    obtain ⟨T, ht, hv⟩ := (an_prefix_iff_l I hZF hB hA ha hJ).mp hl
    exact ⟨T, ht, fun x => (hk x).trans (and_congr_right fun hx =>
      (hv x).trans ⟨And.right, fun h => ⟨hX x hx, h⟩⟩)⟩
  · rintro ⟨T, ht, hk⟩
    obtain ⟨C, hc⟩ := tree_body_exists_l (ZF.modelsKP hZF) A B T
    obtain ⟨L, hl⟩ := pr_exists_l I hZF B J C
    have hL : Atree_d I A B J T L := ⟨ht, C, hc, hl⟩
    refine ⟨L, (an_tree_iff_l I hZF hB hA ha hJ).mpr ⟨T, hL⟩, fun x => ?_⟩
    exact (hk x).trans (and_congr_right fun hx => ((atree_mem_l I hZF hB hA hJ hL x).trans
      ⟨And.right, fun h => ⟨hX x hx, h⟩⟩).symm)

/-- 从 ZF 模型直接构造正规形所用全部空间与配对，无需外加实例参数。 -/
theorem dst_normal_l (hZF : M.Models ZF) : ∃ ω A B J,
    Baire_d I ω B ∧ Fseq_space_d I ω ω A ∧ M.CardinalLessOrEqual I A ω ∧ Npair_d I ω J ∧
    ∀ K, An_d I ω A B J K ↔ ∃ T, Tree_d A T ∧ ∀ x,
      M.mem x K ↔ M.mem x B ∧ ∃ y, M.mem y B ∧ Tpath_d I ω J T x y := by
  obtain ⟨ω, _, B, _, A, _, hB, _, _, hA, ha, _, _⟩ := ds_spaces_l I hZF
  obtain ⟨J, hJ⟩ := npair_exists_l I hZF hB.1
  exact ⟨ω, A, B, J, hB, hA, ha, hJ, fun _ => an_prefix_iff_l I hZF hB hA ha hJ⟩

end YesMetaZFC.SetTheory.Descriptive
