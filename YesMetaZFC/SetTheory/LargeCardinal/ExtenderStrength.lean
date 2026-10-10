import YesMetaZFC.SetTheory.LargeCardinal.ExtenderLength
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderStrengthBound
import YesMetaZFC.SetTheory.LargeCardinal.RankCover
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderPredicateLimit
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRange

/-! # 指定秩层的覆盖与原谓词一致性恢复

在已证明的原因子像中实际覆盖 Vν 后，传递坍塌固定整个 Vν。目标谓词
由原因子的真实逆像集合构造；交换三角给出源谓词保持，固定性给出秩层一致。
完整谓词 Łoś 经同像比较传递到同一个坍塌嵌入，保留全部内部公式码的初等性。
常值图与坍缩图随证书保留；不可达支撑处的代表计数给出同一目标的缺失子集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ep_strength_d (hZF : M.Models ZF) (ω κ L X R A V j Y q c₀ C W : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ c d N S B i k κ', Smem_d I c X R ∧ Smem_d I d N S ∧ M.TransitiveSet N ∧ Smap_d I ω c d X N i ∧
    Spred_emb_d I ω X A N B i ∧
    Wd_crit_d I X i κ κ' ∧ M.MemberSubset L κ' ∧ M.MemberSubset V N ∧ M.MemberSubset B N ∧
    M.IsSetInjectionFromTo I k N Y ∧
    (∀ x y u v, Rd_entry_d x u k → Rd_entry_d y v k → (M.mem x y ↔ M.mem u v)) ∧
    (∀ y, (∃ z, Rd_entry_d z y k) ↔ ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u y) ∧
    (∀ x, M.mem x V → Rd_entry_d x x k) ∧
    (∀ x y z, Rd_entry_d x y i → (Rd_entry_d y z k ↔ Rd_entry_d x z j)) ∧
    (∀ x y, Rd_entry_d x y i → (M.mem x A ↔ M.mem y B)) ∧
    (∀ x, M.mem x V → (M.mem x A ↔ M.mem x B)) ∧
    Ep_realizer_d hZF ω X q c c₀ C W d N i ∧ ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N

section Construction
variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_strength_l {ω δ κ κ₀ K L X R A Y B j S F J O Z D p T V₀ q c C W ν V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (hδ : M.IsRegularCardinal I δ) (hωδ : M.mem ω δ)
    (hVX : V_d I δ X) (hHX : H_d I δ X) (h : Spred_emb_d I ω X A Y B j) (hY : M.TransitiveSet Y)
    (hc : Wd_crit_d I X j κ κ₀) (hL : M.MemberSubset L κ₀)
    (hκL : M.mem κ L) (hωL : M.mem ω L) (rL : M.IsRegularCardinal I L) (sL : M.IsStrongLimitCardinal I L)
    (hSY : M.MemberSubset S Y) (family : Es_family_d I j κ L S F)
    (hF : Em_family_d ω κ L F) (coherent : Es_coherent_d I ω κ L F)
    (system : Ep_system_d I ω κ L X R F J O Z D p T V₀) (limit : Di_limit_d D p T V₀ q C W)
    (model : Smdl_d I c C W) (collapse : Ep_collapse_d hZF ω X R q c C W) (factor : Ee_factor_d hZF j Y q C W)
    (hV : V_d I ν V) (length : Ep_length_d hZF ω κ L X R j Y q c C W)
    (cover : ∀ x, M.mem x V → ∃ E u, M.mem E C ∧ Rd_entry_d u E q ∧ Ee_node_d j u x)
    (agree : ∀ x, M.mem x V → (M.mem x A ↔ M.mem x B)) : Ep_strength_d hZF ω κ L X R A V j Y q c C W := by
  obtain ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩ := h
  have embed : Spred_emb_d I ω X A Y B j := ⟨c₀, R₀, c₁, R₁, hx, hy, hj⟩
  obtain ⟨g, hg, gs, _, any⟩ := factor
  obtain ⟨_, _, t, _, _, _, _, _, _, _, ht, constants, _⟩ := collapse
  obtain ⟨d₀, W₀, expanded, full, fr⟩ := ep_predicate_limit_l hZFC source hδ hωδ hVX hHX hx hy hj hY hc hL
    hSY family hF coherent system limit model hg any ht.1 constants
  obtain ⟨b, d, N, S, i, k, κ', hm, hn, ht, hi, hk, rel, range, triangle, _, _, crit, bound, realizer⟩ := length
  obtain ⟨t', e', ht', ct, wc, bij, he', comp⟩ := realizer
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF κ
  have missing := ep_inaccessible_bound_l hZFC source (hF.source_l hZF X) system limit hm hn ht hi ct wc bij comp hP
    (ZF.v_power_mem_l I hZF hVX hδ.isLimitOrdinal source.cardinal_mem hP) crit.image bound hκL hωL rL sL
  obtain ⟨hVN, fixed⟩ := mem_embedding_fixed_l hZF ht hk rel (ZF.v_transitive_l I hZF hV)
    (fun x hx => (range x).mpr (cover x hx))
  let ρ := (⟨fun _ => B, fun _ => B⟩ : Env M 1).push k
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 2) (rd_entry0_m (.bound 1) .newest (.bound 2)) }
  obtain ⟨B', bs⟩ := ZF.separation_exists_d hZF φ ρ N
  have spec x : M.mem x B' ↔ M.mem x N ∧ ∃ y, M.mem y B ∧ Rd_entry_d x y k := by
    simpa only [φ, Formula.satisfies_existsMem_iff, rd_entry0_sat_l hZF.1] using! bs x
  have predicate x y (hxy : Rd_entry_d x y k) : M.mem x B' ↔ M.mem y B := (spec x).trans
    ⟨fun ⟨_, z, hz, hxz⟩ => hk.1.1.2 x z y hxz hxy ▸ hz,
      fun hy => ⟨hk.1.input_mem_of_pairMember hxy, y, hy, hxy⟩⟩
  have hBN : M.MemberSubset B' N := fun x hx => ((spec x).mp hx).1
  obtain ⟨e, U, pred⟩ := spred_exists_l I hZF ⟨κ', hi.1.1.output_mem_of_pairMember crit.image⟩ hBN
  have pr x y u v (hx : Rd_entry_d x u k) (hy' : Rd_entry_d y v k) : Rd_entry_d x y U ↔ Rd_entry_d u v R₁ := by
    have eq : x = y ↔ u = v := ⟨fun h => hk.1.1.2 y u v (h ▸ hx) hy', fun h => hk.2 x y v (h ▸ hx) hy'⟩
    have left : Rd_entry_d x y U ↔ M.mem x y ∨ x = y ∧ M.mem x B' :=
      (pred.2.2 x y).trans ⟨fun h => h.2.2, fun h =>
        ⟨hk.1.input_mem_of_pairMember hx, hk.1.input_mem_of_pairMember hy', h⟩⟩
    have right : Rd_entry_d u v R₁ ↔ M.mem u v ∨ u = v ∧ M.mem u B :=
      (hy.2.2 u v).trans ⟨fun h => h.2.2, fun h =>
        ⟨hk.1.output_mem_of_pairMember hx, hk.1.output_mem_of_pairMember hy', h⟩⟩
    exact left.trans ((or_congr (rel x y u v hx hy') (and_congr eq (predicate x u hx))).trans right.symm)
  have same y : (∃ E, Rd_entry_d E y g) ↔ ∃ x, Rd_entry_d x y k := by
    refine ⟨fun ⟨E, hEy⟩ => ?_, fun hy => ?_⟩
    · obtain ⟨hE, u, hu, hv⟩ := (gs E y).mp hEy
      exact (range y).mpr ⟨E, u, hE, hu, hv⟩
    · obtain ⟨E, u, hE, hu, hv⟩ := (range y).mp hy
      exact ⟨E, (gs E y).mpr ⟨hE, u, hu, hv⟩⟩
  have full' := smap_same_range_l hZF source.omega full hi.1.1 hg hk expanded pred.1 same
    (fun E H z w y y' hEy hHy hzy hwy => (fr E H y y' hEy hHy).trans (pr z w y y' hzy hwy).symm)
    (fun x E z y hxE hxz hEy => by
      obtain ⟨u, a, H, f, Q, hQ, hf, hs, hfH, hp, huE⟩ := constants x E hxE
      obtain ⟨y', _, hxy⟩ := hj.1.1.2.2 x (hi.1.1.input_mem_of_pairMember hxz)
      have eq := ed_constant_value_l hZF source.omega embed source.transitive hY hQ hf hs hxy
        (any u a H f E y huE hp hfH hEy)
      exact (triangle x z y hxz).mpr (eq.symm ▸ hxy))
  refine ⟨b, d, N, S, B', i, k, κ', hm, hn, ht, hi, ⟨c₀, R₀, e, U, hx, pred, full'⟩, crit, bound, hVN,
    fun x hx => ((spec x).mp hx).1, hk, rel, range, fixed, triangle, ?_, ?_,
    ⟨t', e', ht', ct, wc, bij, he', comp⟩, missing⟩
  · intro x y hxy
    obtain ⟨z, _, hyz⟩ := hk.1.2.2 y (hi.1.1.output_mem_of_pairMember hxy)
    exact (spred_predicate_l I hZF source.omega embed ((triangle x y z hxy).mp hyz)).trans (predicate y z hyz).symm
  · intro x hx
    exact (agree x hx).trans (predicate x x (fixed x hx)).symm

end Construction
end YesMetaZFC.SetTheory.LargeCardinal
