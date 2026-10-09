import YesMetaZFC.Model.SetTheory.Internal.EmbeddingCountable

/-! # 逐点固定载体上的集合与图

有界成员公式固定子集；有序对公式固定坐标对；实际函数的全定义域和
逐点值确定整张函数图。关系图只需坐标落在固定载体内。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
theorem Smap_d.fixed_subset_l {ω c d X R Y S j A B : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j)
    (point : ∀ x, M.mem x A → Rd_entry_d x x j) (hB : M.mem B X)
    (sub : M.MemberSubset B A) : Rd_entry_d B B j := by
  obtain ⟨C, _, hBC⟩ := hj.1.1.2.2 B hB
  have inside := (hj.subset_l hZF hω hX hY hm hn hBC hA).mp sub
  have mem x (hx : M.mem x A) : M.mem x B ↔ M.mem x C := by
    have rel := hj.relation_l I hZF hω hm.1 hn.1 (point x hx) hBC
    exact ⟨fun h => ((hn.2 x C).mp (rel.mp ((hm.2 x B).mpr
      ⟨hj.1.1.input_mem_of_pairMember (point x hx), hB, h⟩))).2.2,
      fun h => ((hm.2 x B).mp (rel.mpr ((hn.2 x C).mpr
        ⟨hj.1.1.output_mem_of_pairMember (point x hx), hj.1.1.output_mem_of_pairMember hBC, h⟩))).2.2⟩
  have eq := hZF.1.eq_of_same_members C B fun x =>
    ⟨fun hx => (mem x (inside x hx)).mpr hx, fun hx => (mem x (sub x hx)).mp hx⟩
  exact eq ▸ hBC

theorem Smap_d.kpair_l {ω c d X R Y S j p a b q a' b' : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hpq : Rd_entry_d p q j) (ha : Rd_entry_d a a' j) (hb : Rd_entry_d b b' j) :
    KPair_d M p a b ↔ KPair_d M q a' b' := by
  have tr := smap_delta_l I hZF hω hX hY hm hn hj (n := 3)
    (kpair0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs) (kpair0_delta_l ..)
    ⟨Fin.cases b (Fin.cases a (fun _ => p)), fun _ => p⟩
    ⟨Fin.cases b' (Fin.cases a' (fun _ => q)), fun _ => q⟩ (Fin.cases hb (Fin.cases ha (fun _ => hpq)))
  simpa only [kpair0_sat_l hZF.1] using! tr

theorem Smap_d.fixed_pair_l {ω c d X R Y S j p a b : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hp : M.mem p X) (pair : KPair_d M p a b)
    (ha : Rd_entry_d a a j) (hb : Rd_entry_d b b j) : Rd_entry_d p p j := by
  obtain ⟨q, _, hpq⟩ := hj.1.1.2.2 p hp
  exact kpair_unique_l M hZF.1 ((hj.kpair_l hZF hω hX hY hm hn hpq ha hb).mp pair) pair ▸ hpq

theorem Smap_d.fixed_relation_l {ω c d X R Y S j A f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j)
    (point : ∀ x, M.mem x A → Rd_entry_d x x j) (hf : M.mem f X)
    (rel : M.IsSetRelationOn I f A) : Rd_entry_d f f j := by
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  let ρ (g : M.Domain) : Env M 2 := ⟨Fin.cases g (fun _ => A), fun _ => A⟩
  have read g : Formula.satisfies (ρ g) φ ↔ ∀ p, M.mem p g →
      ∃ a, M.mem a A ∧ ∃ b, M.mem b A ∧ KPair_d M p a b := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) (ρ f) (ρ g) (Fin.cases hfg (fun _ => hA))
  have bound := (read g).mp (tr.mp ((read f).mpr (fun p hp => by
    obtain ⟨a, b, pair⟩ := rel.1 p hp
    have ab := rel.2 a b ⟨p, pair, hp⟩
    exact ⟨a, ab.1, b, ab.2, pair⟩)))
  have entry a b (ha : M.mem a A) (hb : M.mem b A) :=
    hj.entry_l hZF hω hX hY hm hn (point a ha) (point b hb) hfg
  have eq := hZF.1.eq_of_same_members g f fun p => ⟨fun hp => by
    obtain ⟨a, ha, b, hb, pair⟩ := bound p hp
    obtain ⟨q, pq, hq⟩ := (entry a b ha hb).mpr ⟨p, pair, hp⟩
    exact kpair_unique_l M hZF.1 pq pair ▸ hq, fun hp => by
      obtain ⟨a, b, pair⟩ := rel.1 p hp
      have ab := rel.2 a b ⟨p, pair, hp⟩
      obtain ⟨q, pq, hq⟩ := (entry a b ab.1 ab.2).mp ⟨p, pair, hp⟩
      exact kpair_unique_l M hZF.1 pq pair ▸ hq⟩
  exact eq ▸ hfg

/-- 固定载体上的关系若属于初等像，其原像仍是同一张关系图。 -/
theorem Smap_d.relation_preimage_l {ω c d X R Y S j A f g : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hA : Rd_entry_d A A j) (point : ∀ x, M.mem x A → Rd_entry_d x x j)
    (hfg : Rd_entry_d f g j) (rel : M.IsSetRelationOn I g A) : f = g := by
  let φ : Formula 1 2 := Formula.forallMem .newest (Formula.existsMem (.bound 2)
    (Formula.existsMem (.bound 3) (kpair0_m (.bound 2) (.bound 1) .newest)))
  have tr := smap_delta_l I hZF hω hX hY hm hn hj φ (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..))))
    ⟨Fin.cases f (fun _ => A), fun _ => A⟩ ⟨Fin.cases g (fun _ => A), fun _ => A⟩ (Fin.cases hfg (fun _ => hA))
  simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1] at tr
  have shape := tr.mpr (fun p hp => by
    obtain ⟨a, b, pair⟩ := rel.1 p hp
    have ab := rel.2 a b ⟨p, pair, hp⟩
    exact ⟨a, ab.1, b, ab.2, pair⟩)
  have small : M.IsSetRelationOn I f A := ⟨fun p hp =>
    (shape p hp).elim fun a ha => ha.2.elim fun b hb => ⟨a, b, hb.2⟩, fun a b ⟨p, pair, hp⟩ => by
      obtain ⟨x, hx, y, hy, code⟩ := shape p hp
      obtain ⟨rfl, rfl⟩ := kpair_injective_l M code pair
      exact ⟨hx, hy⟩⟩
  exact hj.1.1.1.2 f f g (hj.fixed_relation_l hZF hω hX hY hm hn hA point
    (hj.1.1.input_mem_of_pairMember hfg) small) hfg

/-- 值域无需整体固定；固定定义域和每个实际函数值已经足够。 -/
theorem Smap_d.fixed_function_l {ω c d X R Y S j D B f : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hD : Rd_entry_d D D j) (point : ∀ x, M.mem x D → Rd_entry_d x x j)
    (hB : M.mem B X) (hf : M.mem f X) (fn : Fn0_d D B f)
    (values : ∀ x y, Rd_entry_d x y f → Rd_entry_d y y j) : Rd_entry_d f f j := by
  obtain ⟨C, _, hBC⟩ := hj.1.1.2.2 B hB
  obtain ⟨g, _, hfg⟩ := hj.1.1.2.2 f hf
  have second := (hj.function_l hZF hω hX hY hm hn hD hBC hfg).mp fn
  have eq := second.ext_l hZF.1 fn fun x hx => by
    obtain ⟨y, _, hxy⟩ := fn.2.1 x hx
    exact ⟨y, (hj.entry_l hZF hω hX hY hm hn (point x hx) (values x y hxy) hfg).mp hxy, hxy⟩
  exact eq ▸ hfg

end YesMetaZFC.SetTheory.Internal
