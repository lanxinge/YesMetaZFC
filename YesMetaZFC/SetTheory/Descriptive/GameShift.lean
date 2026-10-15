import YesMetaZFC.SetTheory.Descriptive.SequenceCons
import YesMetaZFC.SetTheory.Descriptive.GameParity

/-! # 插入一手后换手的实际策略

新策略在局面 s 查询旧策略于 a⌢s 的值。首手属于旧 I 时必须取旧策略自身的输出；
此后所有回合由内部后继奇偶律对应，有限前缀保证策略调用具有因果性。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

theorem gm_shift_l {ω A F z a σ : M.Domain} (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) (strategy : M.IsSetFunctionFromTo I σ F A) :
    ∃ τ, M.IsSetFunctionFromTo I τ F A ∧ ∀ s v, M.PairMember I s v τ ↔
      M.mem s F ∧ ∃ t, Cons_d I z a s t ∧ M.PairMember I t v σ := by
  let ρ : Env M 2 := ⟨fun i => [z, a].get i, fun _ => z⟩
  let φ : BinarySchema 2 := { body := cons_m (𝒞 := 𝒞) (.bound 2) (.bound 3) (.bound 1) .newest }
  have sat s t : φ.denote ρ s t ↔ Cons_d I z a s t := cons_sat_l I hZF.1 ..
  obtain ⟨C, fc, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := F) (by
    intro s hs
    obtain ⟨n, hn, fs⟩ := (space s).mp hs
    obtain ⟨_, t, _, _, _, ct⟩ := cons_exists_l I hZF hw hz ha hn fs
    exact ⟨t, (sat s t).mpr ct⟩)
    (fun _ _ _ _ ht hu => cons_unique_l I hZF.1 ((sat ..).mp ht) ((sat ..).mp hu)) (by
      intro s t hs ht
      obtain ⟨n, hn, fs⟩ := (space s).mp hs
      obtain ⟨k, hk, _, ft⟩ := cons_type_l I hZF hw hz ha hn fs ((sat s t).mp ht)
      exact (space t).mpr ⟨k, hk, ft⟩)
  obtain ⟨τ, fτ, values⟩ := ZF.exists_compositionFunction hZF I fc strategy
  refine ⟨τ, fτ, fun s v => (values s v).trans (and_congr_right fun hs => ?_)⟩
  exact exists_congr fun t => and_congr_left fun _ => ((graph s t).trans
    ((and_congr_right fun _ => sat s t).trans ⟨And.right, fun h => ⟨hs, h⟩⟩))

theorem gm_shift_follows_l {b : Bool} {ω A F z a σ τ f g : M.Domain}
    (hw : M.IsOmega ω) (hz : ∀ x, ¬ M.mem x z) (ha : M.mem a A)
    (values : ∀ s v, M.PairMember I s v τ ↔ M.mem s F ∧ ∃ t, Cons_d I z a s t ∧ M.PairMember I t v σ)
    (first : b = true → M.PairMember I z a σ) (ff : M.IsSetFunctionFromTo I f ω A)
    (fg : M.IsSetFunctionFromTo I g ω A) (cons : Cons_d I z a f g)
    (follow : Gm_follows_d I (!b) ω τ f) : Gm_follows_d I b ω σ g := by
  intro j hj turn s cut v jv
  rcases omega_zero_or_succ_l hZF hw hz hj with eq | ⟨i, hi, sj⟩
  · subst j
    have eq : s = z := hZF.1.eq_of_same_members s z fun q => iff_of_false (fun hq => by
      obtain ⟨i, x, c⟩ := cut.1 q hq
      exact hz i ((cut.2 i x).mp ⟨q, c, hq⟩).1) (hz q)
    subst s
    have ev : v = a := ((cons.2 z v).mp jv).elim And.right (fun ⟨i, _, sz⟩ => (hz i sz.predecessor_mem).elim)
    subst v
    cases b
    · exact (turn (gm_even_zero_l I hZF hw hz)).elim
    · exact first rfl
  · obtain ⟨r, fr, rf, _⟩ := ds_prefix_l I hZF hw ff hi
    obtain ⟨k, t, _, sk, ft, ct⟩ := cons_exists_l I hZF hw hz ha hi fr
    have eq := sk.eq hZF.1 sj; subst k
    have tg := (cons_subset_l I hZF hw hz hi fr ct cons).mpr ⟨rfl, (ds_restrict_iff_l I fr ff.1).mp rf⟩
    have eq := ((ds_restrict_iff_l I ft fg.1).mpr tg).eq hZF.1 cut; subst s
    have rv := follow i hi ((gm_turn_successor_l I hZF b hw hi sj).mp turn) r rf v
      ((cons.successor_l I hZF hw hz hi sj).mp jv)
    obtain ⟨_, u, cu, uv⟩ := (values r v).mp rv
    exact cons_unique_l I hZF.1 cu ct ▸ uv

end YesMetaZFC.SetTheory.Descriptive
