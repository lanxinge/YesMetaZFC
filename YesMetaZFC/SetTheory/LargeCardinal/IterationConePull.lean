import YesMetaZFC.SetTheory.LargeCardinal.IterationProjection
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed

/-! # 回拉图表的子集关系在同一锥中保持

先用壳图恢复原箭头，再以锥交换律识别两条腿上的像。只使用实际传递
隶属结构和全初等图，不要求极限目标满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_pull_subset_d (G π P : M.Domain) : Prop := ∀ i j f a a' b b' c p q x y,
  It_map_d G i j f → Rd_entry_d a a' π → Rd_entry_d b b' π → Rd_entry_d a' c f →
    M.MemberSubset c b' → Rd_entry_d i p P → Rd_entry_d j q P →
    Rd_entry_d a x p → Rd_entry_d b y q → M.MemberSubset x y

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 同一原箭头的两端回拉后，锥交换律使它们在极限中的像相等。 -/
theorem it_cone_pull_entry_l {ω B R b U S u π T Q G Q₀ G₀ A d N W P i j f a a' b₀ b' p q x y : M.Domain}
    (hw : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (hj : Smap_d I ω b u B U π)
    (hωB : M.mem ω B) (hG : Rd_entry_d G₀ G π)
    (small : It_diagram_d hZF ω ω T Q₀ G₀) (big : It_diagram_d hZF ω ω T Q G)
    (cone : It_embedding_d hZF ω A Q₀ G₀ d N W P)
    (hf : It_map_d G i j f) (haa : Rd_entry_d a a' π) (hbb : Rd_entry_d b₀ b' π)
    (image : Rd_entry_d a' b' f) (hp : Rd_entry_d i p P) (hq : Rd_entry_d j q P)
    (hax : Rd_entry_d a x p) (hby : Rd_entry_d b₀ y q) : x = y := by
  have order := big.map_bound_l hZF hf
  have bounds := big.order.bound i j order
  obtain ⟨g, hg⟩ := small.map_l hZF order
  obtain ⟨r, pair, hr⟩ := hg
  have own := rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hG) hr
  have nat := hj.natural_l hZF hw bt ut mb mu hωB
  have fixed := hj.fixed_pair_l hZF hw bt ut mb mu own.1 pair (nat i bounds.1) (nat j bounds.2)
  obtain ⟨g', _, hgg⟩ := hj.1.1.2.2 g own.2
  have map : It_map_d G i j g' := ⟨r, pair, (hj.entry_l hZF hw bt ut mb mu fixed hgg hG).mp hr⟩
  have eq := big.map_unique_l hZF map hf
  subst g'
  have entry := (hj.entry_l hZF hw bt ut mb mu haa hbb hgg).mpr image
  obtain ⟨c, X, R₀, hc, mx⟩ := small.model_l hZF bounds.1
  exact (cone.elementary i p c X R₀ hp hc mx).1.1.1.2 a x y hax
    (cone.commute i j g p q ⟨r, pair, hr⟩ hp hq a b₀ y entry hby)

theorem it_cone_pull_subset_l {ω B R b U S u π T Q G Q₀ G₀ A d N W P : M.Domain}
    (hw : M.IsOmega ω) (bt : M.TransitiveSet B) (ut : M.TransitiveSet U) (nt : M.TransitiveSet N)
    (mb : Smem_d I b B R) (mu : Smem_d I u U S) (mn : Smem_d I d N W)
    (hj : Smap_d I ω b u B U π) (hωB : M.mem ω B) (hQ : M.mem Q₀ B) (hG : Rd_entry_d G₀ G π)
    (small : It_diagram_d hZF ω ω T Q₀ G₀) (big : It_diagram_d hZF ω ω T Q G)
    (models : ∀ i c, Rd_entry_d i c Q₀ → ∃ X R, Smem_d I c X R ∧ M.TransitiveSet X)
    (cone : It_embedding_d hZF ω A Q₀ G₀ d N W P) : It_pull_subset_d G π P := by
  intro i j f a a' b' b'' z p q x y hf haa hbb haz sub hp hq hax hby
  have order := big.map_bound_l hZF hf
  have bounds := big.order.bound i j order
  obtain ⟨g, hg⟩ := small.map_l hZF order
  obtain ⟨r, pair, hr⟩ := hg
  have own := rd_entry_transitive_l bt (hj.1.1.input_mem_of_pairMember hG) hr
  have nat := hj.natural_l hZF hw bt ut mb mu hωB
  have fixed := hj.fixed_pair_l hZF hw bt ut mb mu own.1 pair (nat i bounds.1) (nat j bounds.2)
  obtain ⟨g', _, hgg⟩ := hj.1.1.2.2 g own.2
  have image : It_map_d G i j g' := ⟨r, pair, (hj.entry_l hZF hw bt ut mb mu fixed hgg hG).mp hr⟩
  have eq := big.map_unique_l hZF image hf
  subst g'
  obtain ⟨c, hc⟩ := (small.model_domain i).mp bounds.1
  obtain ⟨e, he⟩ := (small.model_domain j).mp bounds.2
  obtain ⟨X, R₀, mx, xt⟩ := models i c hc
  obtain ⟨Y, S₀, my, yt⟩ := models j e he
  have left := cone.elementary i p c X R₀ hp hc mx.1
  have right := cone.elementary j q e Y S₀ hq he my.1
  have edge := small.elementary i j g c X R₀ e Y S₀ ⟨r, pair, hr⟩ hc he mx.1 my.1
  obtain ⟨v, hv, hav⟩ := edge.1.1.2.2 a (left.1.1.input_mem_of_pairMember hax)
  have hYB := (my.1.1.mem_l M bt (rd_entry_transitive_l bt hQ he).2).1
  obtain ⟨v', _, hvv⟩ := hj.1.1.2.2 v (bt Y hYB v hv)
  have image := (hj.entry_l hZF hw bt ut mb mu haa hvv hgg).mp hav
  obtain ⟨c', X', R', hc', mx'⟩ := big.model_l hZF bounds.1
  obtain ⟨e', Y', S', he', my'⟩ := big.model_l hZF bounds.2
  have original := big.elementary i j f c' X' R' e' Y' S' hf hc' he' mx' my'
  have eq := original.1.1.1.2 a' v' z image haz
  subst v'
  have smaller := (hj.subset_l hZF hw bt ut mb mu hvv hbb).mpr sub
  obtain ⟨w, _, hvw⟩ := right.1.1.2.2 v hv
  have eq := left.1.1.1.2 a w x (cone.commute i j g p q ⟨r, pair, hr⟩ hp hq a v w hav hvw) hax
  subst w
  exact (right.subset_l hZF hw yt nt my mn hvw hby).mp smaller

end YesMetaZFC.SetTheory.LargeCardinal
