import YesMetaZFC.SetTheory.LargeCardinal.Extender.TreeBranch
import YesMetaZFC.Model.SetTheory.Source.Transport
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.DirectedSystem.ElementaryFactor
import YesMetaZFC.Model.SetTheory.ReducedPower.CopyConstant

/-! # 代表复制与有限坐标拉回交换

内部自然数和自然数之间的有限图逐点固定。拉回方程是纯语言中的三个
全称量词加有界矩阵；有限函数闭性保证目标中的每个新坐标列都被量化到。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_function_image_l {ω κ κ' K K' X R Y S c d π n f f' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hnω : M.mem n ω) (hff : Rd_entry_d f f' π)
    (hf : Ep_fun_d κ X n f) : Ep_fun_d κ' Y n f' := by
  obtain ⟨D, hd, hf⟩ := hf
  have hDX := source.space_mem_l hZF hnω hd
  obtain ⟨D', _, hDD⟩ := hπ.1.1.2.2 D hDX
  exact ⟨D', ep_space_map_l hZF source target hm hn hπ hκ hnω hd hDD,
    (hπ.sfun_l hZF source.omega source.transitive target.transitive hm hn hDD hff
      (source.function_l hZF (hπ.1.1.input_mem_of_pairMember hff) hf)).function_l target.transitive⟩

theorem ep_pull_image_l {ω κ κ' K K' X R Y S c d π m n q f f' g g' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π)
    (hκ : Rd_entry_d κ κ' π) (hmω : M.mem m ω) (hnω : M.mem n ω) (hq : Fn0_d m n q)
    (hff : Rd_entry_d f f' π) (hgg : Rd_entry_d g g' π) (pull : Ep_pull_d κ X m n q f g) :
    Ep_pull_d κ' Y m n q f' g' := by
  have qω := hq.mono_target_l (source.omega.transitive (ZF.modelsKP hZF) n hnω)
  have hqX := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union
    source.omega_mem (source.transitive ω source.omega_mem) hmω qω
  have hqq := hπ.finite_fixed_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem hmω hqX qω
  have nat := hπ.natural_l hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  let nz : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let ny : Nonempty {x // M.mem x Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let φ : Formula 1 9 := .imp (fn0_m (.bound 7) (.bound 6) (.bound 2))
    (.imp (cp0_m (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 2) (.bound 1))
      (.iff (rd_entry0_m (.bound 1) .newest (.bound 4)) (rd_entry0_m (.bound 2) .newest (.bound 3))))
  have delta : φ.IsDelta0 := .imp (fn0_delta_l ..) (.imp (cp0_delta_l ..) (.iff (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
  have read Z (hZ : M.TransitiveSet Z) (hz : Nonempty {x // M.mem x Z}) (ρ : Env (rt_model_l Z hz) 9) :
      Formula.satisfies ρ φ ↔ (Fn0_d (ρ.bound 7).val (ρ.bound 6).val (ρ.bound 2).val →
        Cp0_d (ρ.bound 8).val (ρ.bound 7).val (ρ.bound 6).val (ρ.bound 5).val (ρ.bound 2).val (ρ.bound 1).val →
        (Rd_entry_d (ρ.bound 1).val (ρ.bound 0).val (ρ.bound 4).val ↔ Rd_entry_d (ρ.bound 2).val (ρ.bound 0).val (ρ.bound 3).val)) := by
    apply (rt_model_delta_l hZ hz delta ρ).trans
    simp only [φ, Formula.satisfies_imp_iff, fn0_sat_l hZF.1, cp0_sat_l hZF.1,
      Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1]; rfl
  let ρ : Env M 6 := ⟨Fin.cases g (Fin.cases f (Fin.cases q (Fin.cases κ (Fin.cases n (fun _ => m))))), fun _ => ω⟩
  let η : Env M 6 := ⟨Fin.cases g' (Fin.cases f' (Fin.cases q (Fin.cases κ' (Fin.cases n (fun _ => m))))), fun _ => ω⟩
  have params : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) π :=
    Fin.cases hgg (Fin.cases hff (Fin.cases hqq (Fin.cases hκ (Fin.cases (nat n hnω) (fun _ => nat m hmω)))))
  let ρ' : Env (rt_model_l X nz) 6 := ⟨fun i => ⟨ρ.bound i, hπ.1.1.input_mem_of_pairMember (params i)⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η' : Env (rt_model_l Y ny) 6 := ⟨fun i => ⟨η.bound i, hπ.1.1.output_mem_of_pairMember (params i)⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  obtain ⟨z, hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I hz, hn.empty_pred_l I hz, hπ⟩ nz ny
    (.forallE (.forallE (.forallE φ))) (by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]) ρ' η' params
  simp only [Formula.satisfies_forall_iff, read X source.transitive nz, read Y target.transitive ny] at tr
  have next := tr.mp (fun s r x hs hsr => (pull.2.2 s.val r.val hs hsr x.val).symm)
  refine ⟨ep_function_image_l hZF source target hm hn hπ hκ hmω hff pull.1,
    ep_function_image_l hZF source target hm hn hπ hκ hnω hgg pull.2.1, fun s r hs hsr x => ?_⟩
  have hsY := sc_finite_function_l (ZF.modelsKP hZF) target.omega target.transitive (target.algebra_l (ZF.modelsKP hZF)).pair (target.algebra_l (ZF.modelsKP hZF)).union target.omega_mem (target.transitive κ' target.cardinal_mem) hnω hs
  have hrY := sc_finite_function_l (ZF.modelsKP hZF) target.omega target.transitive (target.algebra_l (ZF.modelsKP hZF)).pair (target.algebra_l (ZF.modelsKP hZF)).union target.omega_mem (target.transitive κ' target.cardinal_mem) hmω hsr.1
  by_cases hx : M.mem x Y
  · exact (next ⟨s, hsY⟩ ⟨r, hrY⟩ ⟨x, hx⟩ hs hsr).symm
  · exact iff_of_false (fun h => hx (rd_entry_transitive_l target.transitive (hπ.1.1.output_mem_of_pairMember hgg) h).2)
      (fun h => hx (rd_entry_transitive_l target.transitive (hπ.1.1.output_mem_of_pairMember hff) h).2)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双映射复制的带支撑代表方程 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_node_d (π σ q u E : M.Domain) : Prop := ∃ a B a' D v, KPair_d M u a B ∧ Rd_entry_d a a' σ ∧
  Ec_class_d π B D ∧ KPair_d M v a' D ∧ Rd_entry_d v E q

def ec_node_m {d} (π σ q u E : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.conj (kpair_m (w u) (.bound 4) (.bound 3))
    (.conj (rd_entry_m (.bound 4) (.bound 2) (w σ)) (.conj (ec_class_m (w π) (.bound 3) (.bound 1))
      (.conj (kpair_m .newest (.bound 2) (.bound 1)) (rd_entry_m .newest (w E) (w q))))))))))
derive_free_closed ec_node_m

theorem ec_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (π σ q u E : Term d) :
    Formula.satisfies ρ (ec_node_m π σ q u E) ↔
      Ec_node_d (π.eval ρ) (σ.eval ρ) (q.eval ρ) (u.eval ρ) (E.eval ρ) := by
  simp only [ec_node_m, Ec_node_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, ec_class_sat_l hE, Definitional.Term.eval_weaken]; rfl

/-- 同一对极限上的完整复制证书，包括实际常值方块、唯一性与良基性回传。 -/
def Ec_limit_d (hZF : M.Models ZF) (ω c X d Y π σ q q' e C W e' C' W' : M.Domain) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF)
  ∃ τ i i', Smap_d I ω e e' C C' τ ∧
      Smap_d I ω c e X C i ∧ Smap_d I ω d e' Y C' i' ∧
      (∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q' u E) ∧
      (∀ x x' B E, Rd_entry_d x x' π → Rd_entry_d x B i → (Rd_entry_d B E τ ↔ Rd_entry_d x' E i')) ∧
      (∀ k, Fn0_d C C' k → (∀ u B E, Rd_entry_d u B q → Ec_node_d π σ q' u E → Rd_entry_d B E k) → k = τ) ∧
      (Wf_rel_d C' W' → Wf_rel_d C W)
end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双映射复制整个有限支撑超幂

节点 (a,[f]) 送到 (σ(a),[π(f)]) 的目标极限值。分量复制保证代表无关，
两种搬运与坐标拉回的交换保证过渡相容；实际内部节点图随后唯一下降。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F'
      J O Z D p T V q e C W J' O' Z' D' p' T' V' q' e' C' W' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hπ : Smap_d I ω c d X Y π) (hκ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N') (h₀ : Smem_d I b N R₀) (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ) (theory : Sc_theory_d I ω N R₀) (hωN : M.mem ω N)
    (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L X F) (family' : Em_source_d ω κ' L' Y F')
    (coherent : Ec_source_d I ω κ L X F) (coherent' : Ec_source_d I ω κ' L' Y F') (agree : Ea_maps_d ω κ X π σ)
    (h : Ep_system_d I ω κ L X R F J O Z D p T V) (limit : Di_limit_d D p T V q C W) (model : Smdl_d I e C W)
    (h' : Ep_system_d I ω κ' L' Y S F' J' O' Z' D' p' T' V') (limit' : Di_limit_d D' p' T' V' q' C' W')
    (model' : Smdl_d I e' C' W') : Ec_limit_d hZF ω c X d Y π σ q q' e C W e' C' W' := by
  obtain ⟨Q, hz⟩ := h.codes
  have models := h.components
  obtain ⟨Q', hz'⟩ := h'.codes
  have models' := h'.components
  have image a (ha : M.mem a J) : ∃ a', Rd_entry_d a a' σ ∧ M.mem a' J' := by
    obtain ⟨n, hnω, hna, _⟩ := (h.indices a).mp ha
    obtain ⟨U, haU⟩ := family.total n a hnω hna
    obtain ⟨a', _, haa⟩ := hσ.1.1.2.2 a (rd_entry_transitive_l owner (hσ.1.1.input_mem_of_pairMember hF) haU).1
    exact ⟨a', haa, (h'.indices a').mpr (ec_support_image_l hZF source.omega owner owner' h₀ h₁ hσ hωN hL haa ((h.indices a).mp ha))⟩
  have component a a' o o' (haa : Rd_entry_d a a' σ) (hao : Rd_entry_d a o Z) (hao' : Rd_entry_d a' o' Z') :=
    ec_component_l hZF source target hm hn hπ hκ owner owner' h₀ h₁ hσ hωN hL hF family family' agree haa
      (models a o hao) (models' a' o' hao')
  -- 每个原分量先复制到 σ(a) 分量，再进入目标极限。
  have into a o (hao : Rd_entry_d a o Z) : ∃ A R k, Smdl_d I o A R ∧ Smap_d I ω o e' A C' k ∧
      ∀ u B E, KPair_d M u a B → (Rd_entry_d B E k ↔ M.mem B A ∧ Ec_node_d π σ q' u E) := by
    obtain ⟨a', haa, haJ⟩ := image a (hz.bound_l hao).1
    obtain ⟨o', _, hao'⟩ := hz'.2.1 a' haJ
    obtain ⟨A, R, A', R', s, ma, ma', hs, ss, _⟩ := component a a' o o' haa hao hao'
    obtain ⟨t, ht, ts⟩ := ep_stage_embedding_l hZF target.omega h'.toEg_graph_d h'.diagram limit'
      (h'.toEp_graph_d.elementary_l hZF target family' coherent') model' hao' ma'
    obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF hs ht
    refine ⟨A, R, k, ma, hk, fun u B E hu => (ks B E).trans ?_⟩
    apply and_congr_right
    intro hBA
    constructor
    · rintro ⟨B', hBB, hBE⟩
      obtain ⟨_, _, hc⟩ := (ss B B').mp hBB
      obtain ⟨_, v, hv, hvE⟩ := (ts B' E).mp hBE
      exact ⟨a, B, a', B', v, hu, haa, hc, hv, hvE⟩
    · rintro ⟨a₀, B₀, a₁, B', v, hu₀, ha₁, hc, hv, hvE⟩
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M hu hu₀
      have eq := hσ.1.1.1.2 a a₁ a' ha₁ haa
      subst a₁
      have hB' := (ep_at_read_l hz' hao' ma'.1).mp (h'.toEp_graph_d.at_l (limit'.projection.bound_l hvE).1 hv)
      exact ⟨B', (ss B B').mpr ⟨hBA, hB', hc⟩, (ts B' E).mpr ⟨hB', v, hv, hvE⟩⟩
  have atMap u (hu : M.mem u D) : ∃ a B o A k, KPair_d M u a B ∧ M.mem B A ∧
      Smap_d I ω o e' A C' k ∧ ∀ E, Rd_entry_d B E k ↔ Ec_node_d π σ q' u E := by
    obtain ⟨a, B, hup, hat⟩ := (h.nodes u).mp hu
    obtain ⟨o, A, R, hao, _, ma, hBA⟩ := ep_at_model_l hZF models hat
    obtain ⟨A₀, R₀, k, ma₀, hk, spec⟩ := into a o hao
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I ma₀ ma
    exact ⟨a, B, o, A₀, k, hup, hBA, hk, fun E => (spec u B E hup).trans ⟨And.right, fun h => ⟨hBA, h⟩⟩⟩
  let ρ := ((⟨fun _ => q', fun _ => q'⟩ : Env M 1).push σ).push π
  let φ : BinarySchema 3 := { body := ec_node_m (.bound 2) (.bound 3) (.bound 4) (.bound 1) .newest }
  have sat u E : φ.denote ρ u E ↔ Ec_node_d π σ q' u E := ec_node_sat_l hZF.1 ..
  obtain ⟨f, hf, fs⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := C')
    (fun u hu => by
      obtain ⟨_, B, _, _, _, _, hb, hk, spec⟩ := atMap u hu
      obtain ⟨E, _, hBE⟩ := hk.1.1.2.2 B hb
      exact ⟨E, (sat u E).mpr ((spec E).mp hBE)⟩)
    (fun u hu E H he hh => by
      obtain ⟨_, B, _, _, _, _, _, hk, spec⟩ := atMap u hu
      exact hk.1.1.1.2 B E H ((spec E).mpr ((sat u E).mp he)) ((spec H).mpr ((sat u H).mp hh)))
    (fun u E hu he => by
      obtain ⟨_, _, _, _, _, _, _, hk, spec⟩ := atMap u hu
      exact hk.1.1.output_mem_of_pairMember ((spec E).mpr ((sat u E).mp he)))
  have spec u E := (fs u E).trans (and_congr_right fun _ => sat u E)
  -- 同时搬运坐标和代表，使节点图与原过渡严格交换。
  have comm u v E H (huv : Rd_entry_d u v T) (huE : Rd_entry_d u E f) (hvH : Rd_entry_d v H f) : E = H := by
    obtain ⟨a, B, a', B', u', hu, haa, classB, hu', hu'E⟩ := ((spec u E).mp huE).2
    obtain ⟨a₁, B₁, a₁', B₁', v', hv, hbb, classC, hv', hv'H⟩ := ((spec v H).mp hvH).2
    obtain ⟨f₀, f₁, hf₀, hf₁, hff⟩ := classB
    obtain ⟨m, n, r, g₀, hmω, hnω, hr, hnb, hra, hg₀, pull⟩ := h.representatives u v a a₁ B B₁ hu hv huv f₀ hf₀
    obtain ⟨o, A, R, hao, mo, ma, hBA⟩ := ep_at_model_l hZF models (h.toEp_graph_d.at_l (hf.input_mem_of_pairMember hvH) hv)
    obtain ⟨_, _, _, _, reps⟩ := ep_representatives_l I hZF.1 family mo ma hBA
    obtain ⟨g₁, _, hgg⟩ := hπ.1.1.2.2 g₀ (reps g₀ hg₀).1
    obtain ⟨o', A', R', hao', mo', ma', hBA'⟩ := ep_at_model_l hZF models' (h'.toEp_graph_d.at_l (limit'.projection.bound_l hv'H).1 hv')
    obtain ⟨A₀, R₀, A₁, R₁, _, ma₀, ma₁, _, _, all⟩ := component a₁ a₁' o o' hbb hao hao'
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I ma₀ ma
    obtain ⟨rfl, rfl⟩ := smdl_unique_l I ma₁ ma'
    have hg₁ := all B₁ B₁' g₀ g₁ hBA hBA' classC hg₀ hgg
    have idx := ec_index_image_l hZF source.omega owner owner' h₀ h₁ hσ theory hωN hL haa hbb hmω hnω hr hnb hra
    have copied := ep_pull_image_l hZF source target hm hn hπ hκ hmω hnω hr hff hgg pull
    have edge : Rd_entry_d u' v' T' := (h'.toEp_graph_d.arrow_l hu' hv').mpr
      ⟨(limit'.projection.bound_l hu'E).1, (limit'.projection.bound_l hv'H).1,
        m, n, r, f₁, g₁, hmω, hnω, hr, idx.1, idx.2, hf₁, hg₁, copied⟩
    exact limit'.commute_l h'.diagram edge hu'E hv'H
  have cone i o A R (stage : Di_stage_d I D p V i o A R) :
      ∃ k, Smap_d I ω o e' A C' k ∧ ∀ u E, Rd_entry_d u E k ↔ M.mem u A ∧ Rd_entry_d u E f := by
    obtain ⟨u, hu⟩ := stage.1.2.1
    obtain ⟨o₀, _, hio⟩ := hz.2.1 i (h.projection.bound_l ((stage.2.1 u).mp hu).2).2
    obtain ⟨A₀, R₀, t, ma, ht, ts⟩ := into i o₀ hio
    obtain ⟨s, _, hs, _, ss, _⟩ := ep_tag_l hZF source.omega h.codes h.nodes h.index
      h.toEg_graph_d.label_l h.toEg_graph_d.relation_l stage hio ma
    obtain ⟨k, hk, ks⟩ := smap_comp_l I hZF hs ht
    refine ⟨k, hk, fun u E => (ks u E).trans (and_congr_right fun hu => ?_)⟩
    constructor
    · rintro ⟨B, huB, hBE⟩
      exact (spec u E).mpr ⟨((stage.2.1 u).mp hu).1, ((ts u B E ((ss u B).mp huB).2).mp hBE).2⟩
    · intro huE
      obtain ⟨B, hBA, huB⟩ := hs.1.1.2.2 u hu
      exact ⟨B, huB, (ts u B E ((ss u B).mp huB).2).mpr ⟨hBA, ((spec u E).mp huE).2⟩⟩
  obtain ⟨τ, hτ, law, unique⟩ := di_factor_elementary_l hZF source.omega h.diagram limit
    (h.toEp_graph_d.elementary_l hZF source family coherent) model model' (fn0_of_function_l (ZF.modelsKP hZF) hf) comm cone
  -- 在 a 与 σ(a) 分量上实际构造两条常值嵌入，核验整个复制方块。
  obtain ⟨B₀, hB₀⟩ := model.2.1
  obtain ⟨u₀, hu₀⟩ := (limit.range B₀).mp hB₀
  obtain ⟨a, B, hup, hat⟩ := (h.nodes u₀).mp (limit.projection.bound_l hu₀).1
  obtain ⟨o, _, _, hao, _, _, _⟩ := ep_at_model_l hZF models hat
  obtain ⟨a', haa, haJ⟩ := image a (hz.bound_l hao).1
  obtain ⟨o', _, hao'⟩ := hz'.2.1 a' haJ
  obtain ⟨c₀, i, n, D₀, U₀, G₀, r₀, H₀, V₀, mc, hi, hnω, ha, space, haU, hG₀, md₀, is⟩ :=
    ep_constant_limit_l hZF source family h limit model (h.toEp_graph_d.elementary_l hZF source family coherent) hao
  obtain ⟨d₀, i', n', D₁, U₁, G₁, r₁, H₁, V₁, md, hi', _, ha', space', haU', hG₁, md₁, is'⟩ :=
    ep_constant_limit_l hZF target family' h' limit' model' (h'.toEp_graph_d.elementary_l hZF target family' coherent') hao'
  have hi₀ : Smap_d I ω c e X C i := (I).unique mc.1.1 hm.1.1 ▸ hi
  have hi₁ : Smap_d I ω d e' Y C' i' := (I).unique md.1.1 hn.1.1 ▸ hi'
  have hna := (hσ.function_l hZF source.omega owner owner' h₀ h₁
    (hσ.natural_l hZF source.omega owner owner' h₀ h₁ hωN n hnω) hL haa).mp ha
  have en := ha'.domain_eq_l hZF.1 hna
  subst n'
  have hD₀X := source.space_mem_l hZF hnω space
  obtain ⟨D₂, _, hDD⟩ := hπ.1.1.2.2 D₀ hD₀X
  have ds := ep_space_map_l hZF source target hm hn hπ hκ hnω space hDD
  have ed := hZF.1.eq_of_same_members D₂ D₁ (fun s => (ds s).trans (space' s).symm)
  subst D₂
  have square x x' B E (hxx : Rd_entry_d x x' π) (hxB : Rd_entry_d x B i) :
      Rd_entry_d B E τ ↔ Rd_entry_d x' E i' := by
    obtain ⟨_, f₀, A₀, v₀, hf₀, hc₀, hfA₀, hv₀, hv₀B⟩ := (is x B).mp hxB
    obtain ⟨f₁, hfY, hff⟩ := hπ.1.1.2.2 f₀ ((hG₀ f₀).mp hf₀).1
    have sf := source.function_l hZF ((hG₀ f₀).mp hf₀).1 ((hG₀ f₀).mp hf₀).2
    have hGf := (hG₁ f₁).mpr ⟨hfY, (hπ.sfun_l hZF source.omega source.transitive target.transitive hm hn hDD hff sf).function_l target.transitive⟩
    have hc₁ := rs_constant_image_l hZF source.omega source.transitive target.transitive hm hn hπ hDD hxx hff hc₀
    obtain ⟨A₁, hA₁, hfA₁⟩ := md₁.map.projection.2.2 f₁ hGf
    obtain ⟨v₁, hv₁⟩ := (I).total a' A₁
    have hvD := (h'.nodes v₁).mpr ⟨a', A₁, hv₁, o', H₁, V₁, hao', md₁.code.1, hA₁⟩
    obtain ⟨E₀, _, hvE⟩ := limit'.projection.2.1 v₁ hvD
    have hxE := (is' x' E₀).mpr ⟨hπ.1.1.output_mem_of_pairMember hxx, f₁, A₁, v₁, hGf, hc₁, hfA₁, hv₁, hvE⟩
    have hBE := law v₀ B E₀ hv₀B ((spec v₀ E₀).mpr ⟨(limit.projection.bound_l hv₀B).1,
      a, A₀, a', A₁, v₁, hv₀, haa, ⟨f₀, f₁,
      md₀.map.representative_l I (family.at_l hZF.1 haU ha space).base hfA₀,
      md₁.map.representative_l I (family'.at_l hZF.1 haU' ha' space').base hfA₁, hff⟩, hv₁, hvE⟩)
    exact ⟨fun h => hτ.1.1.1.2 B E₀ E hBE h ▸ hxE, fun h => hi'.1.1.1.2 x' E₀ E hxE h ▸ hBE⟩
  refine ⟨τ, i, i', hτ, hi₀, hi₁, fun B E => ⟨?_, ?_⟩, square,
    fun k hk law' => unique k hk (fun u B E hu hE => law' u B E hu ((spec u E).mp hE).2),
    fun hw => wf_of_map_l hZF hw (fn0_of_function_l (ZF.modelsKP hZF) hτ.1.1)
      (fun x y x' y' hxy hx hy => (hτ.relation_l I hZF source.omega model model' hx hy).mp hxy)⟩
  · intro hBE
    have hBC := hτ.1.1.input_mem_of_pairMember hBE
    obtain ⟨u, hu⟩ := (limit.range B).mp hBC
    obtain ⟨H, _, huH⟩ := hf.2.2 u (limit.projection.bound_l hu).1
    have eq := hτ.1.1.1.2 B H E (law u B H hu huH) hBE
    exact ⟨hBC, u, hu, eq ▸ ((spec u H).mp huH).2⟩
  · rintro ⟨_, u, hu, he⟩
    exact law u B E hu ((spec u E).mpr ⟨(limit.projection.bound_l hu).1, he⟩)

/-- 两张原图固定各自的代表和支撑时，同一超幂上的复制图就是恒等图。 -/
theorem ep_copy_identity_l (hZ : M.Models ZF)
    {ω κ L X R F J O Z D p T V q C W π σ τ : M.Domain}
    (family : Em_source_d ω κ L X F) (h : Ep_system_d (kp_pair_l (ZF.modelsKP hZ)) ω κ L X R F J O Z D p T V)
    (limit : Di_limit_d D p T V q C W) (hτ : Fn0_d C C τ)
    (hπ : ∀ f, M.mem f X → Rd_entry_d f f π) (hσ : ∀ a, M.mem a J → Rd_entry_d a a σ)
    (copy : ∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ ∃ u, Rd_entry_d u B q ∧ Ec_node_d π σ q u E) :
    ∀ B E, Rd_entry_d B E τ ↔ M.mem B C ∧ B = E := by
  obtain ⟨_, hz⟩ := h.codes
  have models := h.components
  have fixed B (hBC : M.mem B C) : Rd_entry_d B B τ := by
    obtain ⟨u, hu⟩ := (limit.range B).mp hBC
    obtain ⟨a, H, hup, hat⟩ := (h.nodes u).mp (limit.projection.bound_l hu).1
    obtain ⟨o, A, S, hao, component, model, hHA⟩ := ep_at_model_l hZ models hat
    obtain ⟨_, _, _, ⟨f, hf⟩, reps⟩ := ep_representatives_l _ hZ.1 family component model hHA
    exact (copy B B).mpr ⟨hBC, u, hu, a, H, a, H, u, hup, hσ a (hz.bound_l hao).1,
      ⟨f, f, hf, hf, hπ f (reps f hf).1⟩, hup, hu⟩
  exact fun B E => ⟨fun h => ⟨(hτ.bound_l h).1,
    (fn0_function_l (ZF.modelsKP hZ) hτ).1.2 B B E (fixed B (hτ.bound_l h).1) h⟩,
    fun ⟨hB, e⟩ => e ▸ fixed B hB⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同时施加两侧扩展器并自动复制

调用者给出所属模型中的实际测度图、两侧子集一致性及两张初等图。
两侧源内部超幂、整个复制图和交换方块均由同一个入口实际构造。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ec_ultrapowers_d (hZF : M.Models ZF) (ω κ L X R F κ' L' Y S F' c d π σ : M.Domain) : Prop :=
  ∃ J O Z D p T V q e C W J' O' Z' D' p' T' V' q' e' C' W',
    Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L X R F J O Z D p T V ∧ Di_limit_d D p T V q C W ∧
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) e C W ∧
    Ep_system_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' L' Y S F' J' O' Z' D' p' T' V' ∧ Di_limit_d D' p' T' V' q' C' W' ∧
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) e' C' W' ∧ Ec_limit_d hZF ω c X d Y π σ q q' e C W e' C' W'

section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_copy_apply_l
    {ω κ κ' K K' L L' X R Y S N R₀ N' R₁ c d b b' π σ F F' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R)
    (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ' K' Y S)
    (hm : Smem_d I c X R)
    (hn : Smem_d I d Y S)
    (hπ : Smap_d I ω c d X Y π) (hκ : Rd_entry_d κ κ' π)
    (owner : M.TransitiveSet N) (owner' : M.TransitiveSet N')
    (h₀ : Smem_d I b N R₀)
    (h₁ : Smem_d I b' N' R₁)
    (hσ : Smap_d I ω b b' N N' σ)
    (theory : Sc_theory_d I ω N R₀) (hωN : M.mem ω N)
    (hL : Rd_entry_d L L' σ) (hF : Rd_entry_d F F' σ)
    (family : Em_source_d ω κ L N F) (family' : Em_source_d ω κ' L' N' F')
    (coherent : Ec_source_d I ω κ L N F)
    (coherent' : Ec_source_d I ω κ' L' N' F')
    (agree : Ea_agree_d ω κ N X) (agree' : Ea_agree_d ω κ' N' Y) (maps : Ea_maps_d ω κ X π σ)
    : Ec_ultrapowers_d hZF ω κ L X R F κ' L' Y S F' c d π σ := by
  obtain ⟨J, O, Z, D, p, T, V, q, e, C, W, h, limit, model, _⟩ := ep_apply_l hZF source family coherent agree
  obtain ⟨J', O', Z', D', p', T', V', q', e', C', W', h', limit', model', _⟩ := ep_apply_l hZF target family' coherent' agree'
  exact ⟨J, O, Z, D, p, T, V, q, e, C, W, J', O', Z', D', p', T', V', q', e', C', W', h, limit, model, h', limit', model',
    ep_copy_l hZF source target hm hn hπ hκ owner owner' h₀ h₁ hσ theory hωN hL hF
      (family.transfer_l agree) (family'.transfer_l agree') (coherent.transfer_l hZF agree) (coherent'.transfer_l hZF agree') maps
      h limit model h' limit' model'⟩

end

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 从完整测度图自动得到所属模型 N∈X、跨模型施加条件及两张实际恒等图的复制。 -/
theorem ep_owned_copy_l {ω κ L F : M.Domain}
    (hω : M.IsOmega ω) (hωκ : M.MemberSubset ω κ)
    (family : Em_family_d ω κ L F)
    (coherent : Es_coherent_d I ω κ L F) :
    ∃ K N R₀ K' X R b c π σ,
      Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K N R₀ ∧ Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' X R ∧
      Smem_d I b N R₀ ∧ Smem_d I c X R ∧ M.mem F N ∧ M.mem L N ∧ M.mem N X ∧
      Ea_agree_d ω κ N X ∧ Smap_d I ω c c X X π ∧ Smap_d I ω b b N N σ ∧
      (∀ x y, Rd_entry_d x y π ↔ M.mem x X ∧ x = y) ∧
      (∀ x y, Rd_entry_d x y σ ↔ M.mem x N ∧ x = y) ∧
      Ec_ultrapowers_d hZF ω κ L X R F κ L X R F c c π σ := by
  obtain ⟨A, hA⟩ := KP.exists_pair (ZF.modelsKP hZF) F L
  obtain ⟨K, N, R₀, owner, hAN, full₀⟩ := ep_source_exists_l hZFC A hω hωκ
  obtain ⟨K', X, R, source, hNX, full₁⟩ := ep_source_exists_l hZFC N hω hωκ
  have hFN := owner.transitive A hAN F ((hA F).mpr (Or.inl rfl))
  have hLN := owner.transitive A hAN L ((hA L).mpr (Or.inr rfl))
  have agree : Ea_agree_d ω κ N X := fun n D A hn hD hAD =>
    ⟨fun _ => full₁ n D A hn hD hAD, fun _ => full₀ n D A hn hD hAD⟩
  obtain ⟨b, hn⟩ := owner.code
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨π, hπ, ps⟩ := smap_identity_l I hZF (c := c) (X := X) hω
  obtain ⟨σ, hσ, ss⟩ := smap_identity_l I hZF (c := b) (X := N) hω
  have maps : Ea_maps_d ω κ X π σ := fun n D A B hn hD _ hAD hAB =>
    (ss A B).mpr ⟨full₀ n D A hn hD hAD, ((ps A B).mp hAB).2⟩
  exact ⟨K, N, R₀, K', X, R, b, c, π, σ, owner, source, hn, hm, hFN, hLN, hNX, agree, hπ, hσ, ps, ss,
    ep_copy_apply_l hZF source source hm hm hπ ((ps κ κ).mpr ⟨source.cardinal_mem, rfl⟩)
      owner.transitive owner.transitive hn hn hσ owner.theory owner.omega_mem
      ((ss L L).mpr ⟨hLN, rfl⟩) ((ss F F).mpr ⟨hFN, rfl⟩)
      (family.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) N) (family.source_l (ZF.modelsKP hZF) (fun _ D _ _ => ZF.exists_powerSet hZF D) N) (coherent.source_l I N) (coherent.source_l I N)
      agree agree maps⟩

end YesMetaZFC.SetTheory.LargeCardinal
