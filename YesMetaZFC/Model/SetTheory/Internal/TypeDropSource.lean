import YesMetaZFC.Model.SetTheory.Internal.TypeDropSyntax
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure
import YesMetaZFC.Model.SetTheory.Internal.SeparationSource

/-! # 原语法 dcp 在传递源中的绝对读取

重编码只改变指定常量的名字。两张已有列中的坐标、查询对和投影见证
都由传递性收回源；不要求源模型满足 ZF，也不要求类型先有语义实现。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hE : Extensional M) (hP : ∀ a b : M.Domain, ∃ p, Pair_d M p a b)
  {X : M.Domain} (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
  (pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b)
local notation "N" => rt_model_l X nx
local notation "I" => kpair_interpretation_l M hE hP
local notation "J" => rt_pair_l hX nx hE pair

private theorem rt_td_name_l (n m a b : (N).Domain) : Td_name_d n m a b ↔ Td_name_d n.val m.val a.val b.val := by
  have eq (x y : (N).Domain) : x = y ↔ x.val = y.val := ⟨congrArg Subtype.val, Subtype.ext⟩
  exact or_congr (and_congr (eq a n) (eq b m)) (and_congr (not_congr (eq a n)) (eq b a))

theorem rt_td_column_l (n m E F : (N).Domain) : Td_column_d J n m E F ↔ Td_column_d I n.val m.val E.val F.val := by
  have ent := rt_entry_l hX nx hE
  constructor
  · rintro ⟨rel, read⟩
    refine ⟨(rt_relation_l hE hP hX nx pair F).mp rel, fun i b => ⟨?_, ?_⟩⟩
    · intro hib
      have ib := rd_entry_transitive_l hX F.property hib
      obtain ⟨a, hia, name⟩ := (read ⟨i, ib.1⟩ ⟨b, ib.2⟩).mp ((ent ..).mpr hib)
      exact ⟨a.val, (ent ..).mp hia, (rt_td_name_l nx ..).mp name⟩
    · rintro ⟨a, hia, name⟩
      have ia := rd_entry_transitive_l hX E.property hia
      have hb : M.mem b X := name.elim (fun h => h.2.symm ▸ m.property) (fun h => h.2.symm ▸ ia.2)
      exact (ent ..).mp ((read ⟨i, ia.1⟩ ⟨b, hb⟩).mpr ⟨⟨a, ia.2⟩, (ent ..).mpr hia, (rt_td_name_l nx ..).mpr name⟩)
  · rintro ⟨rel, read⟩
    refine ⟨(rt_relation_l hE hP hX nx pair F).mpr rel, fun i b => ⟨?_, ?_⟩⟩
    · intro hib
      obtain ⟨a, hia, name⟩ := (read i.val b.val).mp ((ent ..).mp hib)
      exact ⟨⟨a, (rd_entry_transitive_l hX E.property hia).2⟩, (ent ..).mpr hia, (rt_td_name_l nx ..).mpr name⟩
    · rintro ⟨a, hia, name⟩
      exact (ent ..).mpr ((read i.val b.val).mpr ⟨a.val, (ent ..).mp hia, (rt_td_name_l nx ..).mp name⟩)

theorem rt_td_query_l (n m p q : (N).Domain) : Td_query_d J n m p q ↔ Td_query_d I n.val m.val p.val q.val := by
  have cp := rt_kpair_l hE hP hX nx pair
  constructor
  · rintro ⟨z, E, F, hp, hq, col⟩
    exact ⟨z.val, E.val, F.val, (cp ..).mp hp, (cp ..).mp hq, (rt_td_column_l hE hP hX nx pair ..).mp col⟩
  · rintro ⟨z, E, F, hp, hq, col⟩
    have zE := hp.mem_l M hX p.property
    have zF := hq.mem_l M hX q.property
    exact ⟨⟨z, zE.1⟩, ⟨E, zE.2⟩, ⟨F, zF.2⟩, (cp ..).mpr hp, (cp ..).mpr hq,
      (rt_td_column_l hE hP hX nx pair ..).mpr col⟩

theorem rt_td_project_l (n m D t v : (N).Domain) :
    Td_project_d J n m D t v ↔ Td_project_d I n.val m.val D.val t.val v.val := by
  constructor
  · intro h p
    constructor
    · intro hp
      obtain ⟨hd, q, code, hq⟩ := (h ⟨p, hX v.val v.property p hp⟩).mp hp
      exact ⟨hd, q.val, (rt_td_query_l hE hP hX nx pair ..).mp code, hq⟩
    · rintro ⟨hd, q, code, hq⟩
      exact (h ⟨p, hX D.val D.property p hd⟩).mpr ⟨hd, ⟨q, hX t.val t.property q hq⟩,
        (rt_td_query_l hE hP hX nx pair ..).mpr code, hq⟩
  · intro h p
    exact (h p.val).trans (and_congr_right fun _ =>
      ⟨fun ⟨q, code, hq⟩ => ⟨⟨q, hX t.val t.property q hq⟩, (rt_td_query_l hE hP hX nx pair ..).mpr code, hq⟩,
        fun ⟨q, code, hq⟩ => ⟨q.val, (rt_td_query_l hE hP hX nx pair ..).mp code, hq⟩⟩)

include hX pair in
theorem td_dcp_source_l {d} (ρ : Env N d) (n m D t v : Term d) :
    Formula.satisfies ρ (td_dcp_m n m D t v) ↔
      Td_dcp_d I (n.eval ρ).val (m.eval ρ).val (D.eval ρ).val (t.eval ρ).val (v.eval ρ).val :=
  (td_dcp_sat_l J (rt_model_ext_l hE hX nx) ρ n m D t v).trans
    (and_congr (rt_successor_l hX nx hE ..) (rt_td_project_l hE hP hX nx pair ..))

include hX in
/-- 原投影在源内由相对分离实际产生，重编码见证由传递性绝对读取。 -/
theorem td_project_source_exists_l (hZF : M.Models ZF) {ω c R n m D t : M.Domain}
    (hω : M.IsOmega ω) (model : Smem_d (kp_pair_l (ZF.modelsKP hZF)) c X R)
    (theory : Sc_theory_d (kp_pair_l (ZF.modelsKP hZF)) ω X R)
    (hn : M.mem n X) (hm : M.mem m X) (hD : M.mem D X) (ht : M.mem t X) :
    ∃ v, M.mem v X ∧ Td_project_d (kp_pair_l (ZF.modelsKP hZF)) n m D t v := by
  obtain ⟨x, hx⟩ := model.1.2.1
  let nc : Nonempty {x // M.mem x X} := ⟨⟨x, hx⟩⟩
  let K₀ := kp_pair_l (ZF.modelsKP hZF)
  let P := rt_pair_l hX nc hZF.1 theory.algebra.pair
  let φ : UnarySchema 3 := { body := .existsE (.conj
    (td_query_m (.bound 4) (.bound 3) (.bound 1) .newest) (.mem .newest (.bound 2))) }
  let ρ : Env (rt_model_l X nc) 3 :=
    ⟨Fin.cases ⟨t, ht⟩ (Fin.cases ⟨m, hm⟩ (fun _ => ⟨n, hn⟩)), fun _ => ⟨n, hn⟩⟩
  have read (p : (rt_model_l X nc).Domain) : φ.denote ρ p ↔
      ∃ q, Td_query_d K₀ n m p.val q ∧ M.mem q t := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      td_query_sat_l P (rt_model_ext_l hZF.1 hX nc), Formula.satisfies_mem_iff]
    exact ⟨fun ⟨q, code, hq⟩ => ⟨q.val,
      (rt_td_query_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nc theory.algebra.pair ..).mp code, hq⟩,
      fun ⟨q, code, hq⟩ => ⟨⟨q, hX t ht q hq⟩,
        (rt_td_query_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hX nc theory.algebra.pair ..).mpr code, hq⟩⟩
  obtain ⟨v, hv, sub, sep⟩ := sc_separate_relative_l K₀ hZF hω model theory nc φ ρ hD
  exact ⟨v, hv, fun p => ⟨fun hp => ⟨sub p hp,
    (read ⟨p, hX v hv p hp⟩).mp ((sep ⟨p, hX v hv p hp⟩).mp hp).2⟩,
    fun hp => (sep ⟨p, hX D hD p hp.1⟩).mpr ⟨hp.1, (read ⟨p, hX D hD p hp.1⟩).mpr hp.2⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
