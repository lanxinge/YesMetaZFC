import YesMetaZFC.SetTheory.LargeCardinal.CountableSupport
import YesMetaZFC.SetTheory.Card.FiniteSequenceJoin
import YesMetaZFC.Model.SetTheory.Internal.DirectedSystem.Basic

/-! # 全部有限支撑的定向索引

索引采用不重复的内部有限列；允许任意排列。支撑包含的坐标映射由目标列的
单射性唯一确定。任意两个支撑均有共同上界，不截断支撑大小或使用标准有限性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem ec_factor_l (hZF : M.Models ZF) {m n L a b : M.Domain} (ha : Fn0_d m L a)
    (hb : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) b n L)
    (hc : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x b) :
    ∃ q, Fn0_d m n q ∧ Cp0_d m n L q b a := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  let ρ : Env M 2 := (⟨fun _ => a, fun _ => a⟩ : Env M 1).push b
  let φ : BinarySchema 2 := { body := .existsE (.conj (rd_entry_m (.bound 2) .newest (.bound 4))
    (rd_entry_m (.bound 1) .newest (.bound 3))) }
  have sat i j : φ.denote ρ i j ↔ ∃ x, Rd_entry_d i x a ∧ Rd_entry_d j x b := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      rd_entry_sat_l hZF.1]; rfl
  obtain ⟨q, hq, spec⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := m) (target := n)
    (fun i hi => by
      obtain ⟨x, _, hix⟩ := ha.2.1 i hi
      obtain ⟨j, hjx⟩ := hc i x hix
      exact ⟨j, (sat i j).mpr ⟨x, hix, hjx⟩⟩)
    (fun i _ j k hj hk => by
      obtain ⟨x, hix, hjx⟩ := (sat i j).mp hj
      obtain ⟨y, hiy, hky⟩ := (sat i k).mp hk
      have e := (fn0_function_l (ZF.modelsKP hZF) ha).1.2 i y x hiy hix
      exact hb.2 j k x hjx (e ▸ hky))
    (fun i j _ hj => ((sat i j).mp hj).elim fun _ hh => hb.1.input_mem_of_pairMember hh.2)
  refine ⟨q, fn0_of_function_l (ZF.modelsKP hZF) hq, ha, fun i hi => ?_⟩
  obtain ⟨j, hj, hij⟩ := hq.2.2 i hi
  obtain ⟨x, hix, hjx⟩ := (sat i j).mp ((spec i j).mp hij).2
  exact ⟨j, hj, x, (ha.bound_l hix).2, hij, hjx, hix⟩

theorem ec_factor_unique_l (hE : Extensional M) {m n L a b q r : M.Domain}
    (hb : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j)
    (hq : Fn0_d m n q) (hr : Fn0_d m n r) (hqa : Cp0_d m n L q b a) (hra : Cp0_d m n L r b a) : q = r := by
  apply hq.ext_l hE hr
  intro i hi
  obtain ⟨j, _, x, hx, hij, hjx, hix⟩ := hqa.2 i hi
  obtain ⟨k, _, y, hy, hik, hky, hiy⟩ := hra.2 i hi
  have e := hqa.1.2.2 i hi y hy x hx hiy hix
  exact ⟨j, hij, hb k j x (e ▸ hky) hjx ▸ hik⟩

theorem ec_prefix_l (hZF : M.Models ZF) {ω m L a f : M.Domain} (hω : M.IsOmega ω) (hm : M.mem m ω)
    (ha : Fn0_d m L a) (hf : M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) f ω L)
    (hc : ∀ i x, Rd_entry_d i x a → ∃ j, Rd_entry_d j x f) :
    ∃ n b q, M.mem n ω ∧ M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) b n L ∧
      Fn0_d m n q ∧ Cp0_d m n L q b a ∧ M.MemberSubset b f := by
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hf hc
  obtain ⟨n, hn, hqn⟩ := ec_finite_bound_l hZF hω hm hq
  obtain ⟨b, hb⟩ := ZF.exists_restriction hZF (kp_pair_l (ZF.modelsKP hZF)) f n
  have bn := hb.isSetFunctionFromTo hf.1 (hω.transitive hZF n hn)
  have bf := fn0_of_function_l (ZF.modelsKP hZF) bn
  refine ⟨n, b, q, hn, ⟨bn, fun i j x hi hj => hf.2 i j x ((hb.2 i x).mp hi).2 ((hb.2 j x).mp hj).2⟩,
    hqn, ⟨ha, fun i hi => ?_⟩,
    (res0_of_restriction_l (ZF.modelsKP hZF) (fn0_of_function_l (ZF.modelsKP hZF) hf.1) hb).1⟩
  obtain ⟨j, _, x, hx, hij, hjx, hix⟩ := hqa.2 i hi
  exact ⟨j, (hqn.bound_l hij).2, x, hx, hij, (hb.2 j x).mpr ⟨(hqn.bound_l hij).2, hjx⟩, hix⟩

theorem ec_join_l (hZF : M.Models ZF) {ω L m n a b : M.Domain} (hω : M.IsOmega ω)
    (hωL : M.MemberSubset ω L) (hm : M.mem m ω) (hn : M.mem n ω)
    (ha : Fn0_d m L a) (hb : Fn0_d n L b) : ∃ k c q r, M.mem k ω ∧
      M.IsSetInjectionFromTo (kp_pair_l (ZF.modelsKP hZF)) c k L ∧
      Fn0_d m k q ∧ Cp0_d m k L q c a ∧ Fn0_d n k r ∧ Cp0_d n k L r c b := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨l, d, hl, hd, had, hbd⟩ := ZF.fseq_join_l I hZF hω hm hn
    (fn0_function_l (ZF.modelsKP hZF) ha) (fn0_function_l (ZF.modelsKP hZF) hb)
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hd.1 hd.2.1
  have dD : M.IsSetFunctionFromTo I d l D := ⟨hd.1, hd.2.1,
    fun i hi => (hd.2.2 i hi).imp fun x hx => ⟨(hD x).mpr ⟨i, hx.2⟩, hx.2⟩⟩
  have hc := ZF.ordinal_image_bound_l I hZF (hω.isOrdinal hZF)
    (ZF.exists_inclusionInjection hZF I (hω.transitive hZF l hl)) dD
    (fun x hx => ((hD x).mp hx).imp fun i hi => ⟨hd.input_mem_of_pairMember hi, hi⟩)
  obtain ⟨f, hf, cover⟩ := ec_cover_l hZF hω hωL
    (fun x hx => ((hD x).mp hx).elim fun _ hi => hd.output_mem_of_pairMember hi) hc
  obtain ⟨k, c, s, hk, hc, hs, hdsc, _⟩ := ec_prefix_l hZF hω hl (fn0_of_function_l (ZF.modelsKP hZF) hd)
    hf (fun i x hi => cover x ((hD x).mpr ⟨i, hi⟩))
  have covered i x (hix : Rd_entry_d i x d) : ∃ j, Rd_entry_d j x c := by
    obtain ⟨j, _, hij⟩ := hs.2.1 i (hd.input_mem_of_pairMember hix)
    exact ⟨j, (hdsc.value_l hs (fn0_of_function_l (ZF.modelsKP hZF) hc.1) hij).mp hix⟩
  obtain ⟨q, hq, hqa⟩ := ec_factor_l hZF ha hc (fun i x hi => covered i x ((had.2 i x).mp hi).2)
  obtain ⟨r, hr, hrb⟩ := ec_factor_l hZF hb hc (fun i x hi => by
    obtain ⟨_, j, _, hjx⟩ := (hbd.2 i x).mp hi
    exact covered j x hjx)
  exact ⟨k, c, q, r, hk, hc, hq, hqa, hr, hrb⟩

def Ei_d (ω L a : M.Domain) : Prop := ∃ n, M.mem n ω ∧ Fn0_d n L a ∧
  ∀ i j x, Rd_entry_d i x a → Rd_entry_d j x a → i = j

def ei_m {d} (ω L a : Term d) : Formula 1 d := Formula.existsMem ω
  (Formula.isInjectionFromTo kpair_convention_l a.weaken .newest L.weaken)
derive_free_closed ei_m

theorem ei_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (ω L a : Term d) :
    Formula.satisfies ρ (ei_m ω L a) ↔ Ei_d (ω.eval ρ) (L.eval ρ) (a.eval ρ) := by
  simp only [ei_m, Ei_d, Formula.satisfies_existsMem_iff,
    Formula.satisfies_isInjectionFromTo_iff (kp_pair_l hKP) hKP.1, Definitional.Term.eval_weaken]
  exact exists_congr fun n => and_congr_right fun _ =>
    ⟨fun h => ⟨fn0_of_function_l hKP h.1, h.2⟩, fun h => ⟨fn0_function_l hKP h.1, h.2⟩⟩

def Ei_map_d (ω L a b q : M.Domain) : Prop := ∃ m n, M.mem m ω ∧ M.mem n ω ∧
  Fn0_d m n q ∧ Fn0_d n L b ∧ Cp0_d m n L q b a

def ei_map_m {d} (ω L a b q : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (.mem (.bound 1) ω.weaken.weaken) (.conj (.mem .newest ω.weaken.weaken)
    (.conj (fn0_m (.bound 1) .newest q.weaken.weaken) (.conj (fn0_m .newest L.weaken.weaken b.weaken.weaken)
      (cp0_m (.bound 1) .newest L.weaken.weaken q.weaken.weaken b.weaken.weaken a.weaken.weaken))))))
derive_free_closed ei_map_m

theorem ei_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω L a b q : Term d) :
    Formula.satisfies ρ (ei_map_m ω L a b q) ↔
      Ei_map_d (ω.eval ρ) (L.eval ρ) (a.eval ρ) (b.eval ρ) (q.eval ρ) := by
  simp only [ei_map_m, Ei_map_d, Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, Formula.satisfies_conj_iff,
    fn0_sat_l hE, cp0_sat_l hE, Definitional.Term.eval_weaken]; rfl

theorem ei_order_l (hZF : M.Models ZF) {ω L : M.Domain} (hω : M.IsOmega ω) (hωL : M.MemberSubset ω L) :
    ∃ J O, (∀ a, M.mem a J ↔ Ei_d ω L a) ∧ Di_order_d J O ∧
      ∀ a b, Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  obtain ⟨S, hS⟩ := ZF.fseq_space_exists_l I hZF hω L
  let ρ : Env M 2 := (⟨fun _ => ω, fun _ => ω⟩ : Env M 1).push L
  let φ : UnarySchema 2 := { body := ei_m (.bound 2) (.bound 1) .newest }
  obtain ⟨J, hj⟩ := ZF.separation_exists_d hZF φ ρ S
  have hJ a : M.mem a J ↔ Ei_d ω L a := (hj a).trans
    ((and_congr_right fun _ => ei_sat_l (ZF.modelsKP hZF) _ _ _ _).trans
      ⟨And.right, fun h => ⟨(hS a).mpr (h.elim fun n hn => ⟨n, hn.1, fn0_function_l (ZF.modelsKP hZF) hn.2.1⟩), h⟩⟩)
  let ψ : BinarySchema 2 := { body := .existsE (ei_map_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest) }
  obtain ⟨O, _, ho⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ ρ J
  have spec a b : Rd_entry_d a b O ↔ M.mem a J ∧ M.mem b J ∧ ∃ q, Ei_map_d ω L a b q := by
    simpa only [ψ, BinarySchema.denote, Formula.satisfies_exists_iff, ei_map_sat_l hZF.1] using! ho a b
  refine ⟨J, O, hJ, ⟨?_, ?_, fun a b h => ⟨((spec a b).mp h).1, ((spec a b).mp h).2.1⟩, ?_⟩, spec⟩
  · intro a ha
    obtain ⟨m, hm, hma, inj⟩ := (hJ a).mp ha
    obtain ⟨q, hq, hc⟩ := ec_factor_l hZF hma ⟨fn0_function_l (ZF.modelsKP hZF) hma, inj⟩
      (fun i _ hi => ⟨i, hi⟩)
    exact (spec a a).mpr ⟨ha, ha, q, m, m, hm, hm, hq, hma, hc⟩
  · intro a b c hab hbc
    obtain ⟨ha, hb, q, m, n, hm, hn, hq, hnb, hqa⟩ := (spec a b).mp hab
    obtain ⟨_, hc, r, n', l, hn', hl, hr, hlc, hrb⟩ := (spec b c).mp hbc
    have e := hrb.1.domain_eq_l hZF.1 hnb
    subst n'
    obtain ⟨s, hs⟩ := cp0_exists_l (ZF.modelsKP hZF) hq hr
    exact (spec a c).mpr ⟨ha, hc, s, m, l, hm, hl, hs.1, hlc,
      Cp0_d.assoc_l hr hq hs hlc hrb hqa⟩
  · intro a b ha hb
    obtain ⟨m, hm, hma, _⟩ := (hJ a).mp ha
    obtain ⟨n, hn, hnb, _⟩ := (hJ b).mp hb
    obtain ⟨k, c, q, r, hk, hkc, hq, hqa, hr, hrb⟩ := ec_join_l hZF hω hωL hm hn hma hnb
    have hc := (hJ c).mpr ⟨k, hk, fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hkc.2⟩
    exact ⟨c, hc, (spec a c).mpr ⟨ha, hc, q, m, k, hm, hk, hq,
      fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hqa⟩,
      (spec b c).mpr ⟨hb, hc, r, n, k, hn, hk, hr, fn0_of_function_l (ZF.modelsKP hZF) hkc.1, hrb⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal
