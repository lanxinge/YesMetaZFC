import YesMetaZFC.SetTheory.LargeCardinal.IterationDirectLimit
import YesMetaZFC.SetTheory.LargeCardinal.IterationTree

/-! # 极限投影的规范集合图

r 把带标号代表送到目标。各腿由去标签的同一个公式定义，故图唯一，
可由替代一次收集整列；这一步不选择商类代表，也不选择初等嵌入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_project_d (r i f : M.Domain) : Prop := (∀ p, M.mem p f → ∃ x y, KPair_d M p x y) ∧
  ∀ x y, Rd_entry_d x y f ↔ ∃ a, KPair_d M a i x ∧ Rd_entry_d a y r

def it_project_m {d} (r i f : Term d) : Formula 1 d := .conj (Formula.isRelation kpair_convention_l f)
  (.forallE (.forallE (.iff (rd_entry_m (.bound 1) .newest f.weaken.weaken) (.existsE
    (.conj (kpair_m .newest i.weaken.weaken.weaken (.bound 2)) (rd_entry_m .newest (.bound 1) r.weaken.weaken.weaken))))))
derive_free_closed it_project_m

theorem it_project_sat_l (hKP : M.Models KP) {d} (ρ : Env M d) (r i f : Term d) :
    Formula.satisfies ρ (it_project_m r i f) ↔ It_project_d (r.eval ρ) (i.eval ρ) (f.eval ρ) := by
  simp only [it_project_m, It_project_d, Formula.satisfies_conj_iff,
    Formula.satisfies_isRelation_iff (kp_pair_l hKP), Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, kpair_sat_l M hKP.1,
    rd_entry_sat_l hKP.1, Definitional.Term.eval_weaken]; rfl

theorem It_project_d.unique_l (hE : Extensional M) {r i f g : M.Domain}
    (hf : It_project_d r i f) (hg : It_project_d r i g) : f = g := by
  have sub f g (hf : It_project_d r i f) (hg : It_project_d r i g) p (hp : M.mem p f) : M.mem p g := by
    obtain ⟨x, y, hx⟩ := hf.1 p hp
    obtain ⟨q, hq, hqg⟩ := (hg.2 x y).mpr ((hf.2 x y).mp ⟨p, hx, hp⟩)
    exact kpair_unique_l M hE hq hx ▸ hqg
  exact hE.eq_of_same_members f g fun p => ⟨sub f g hf hg p, sub g f hg hf p⟩

structure It_cone_d (hZF : M.Models ZF) (ω B Q G d N W P : M.Domain) : Prop where
  model : Smdl_d (kp_pair_l (ZF.modelsKP hZF)) d N W
  function : M.IsSetFunction (kp_pair_l (ZF.modelsKP hZF)) P
  domain : M.IsDomainOf (kp_pair_l (ZF.modelsKP hZF)) B P
  elementary : ∀ i f c X R, Rd_entry_d i f P → Rd_entry_d i c Q →
    Smdl_d (kp_pair_l (ZF.modelsKP hZF)) c X R → Smap_d (kp_pair_l (ZF.modelsKP hZF)) ω c d X N f
  commute : ∀ i j f u v, It_map_d G i j f → Rd_entry_d i u P → Rd_entry_d j v P →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z v → Rd_entry_d x z u
  cover : ∀ y, M.mem y N → ∃ i f x, Rd_entry_d i f P ∧ Rd_entry_d x y f

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_projects_l {B r : M.Domain} (total : ∀ i, M.mem i B → ∃ f, It_project_d r i f) :
    ∃ P, M.IsSetFunction I P ∧ M.IsDomainOf I B P ∧
      ∀ i f, Rd_entry_d i f P ↔ M.mem i B ∧ It_project_d r i f := by
  let φ : BinarySchema 1 := { body := it_project_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => r, fun _ => r⟩
  have sat i f : φ.denote ρ i f ↔ It_project_d r i f := it_project_sat_l (ZF.modelsKP hZF) ..
  have ht i hi := (total i hi).imp (fun f hf => (sat i f).mpr hf)
  have unique i f g (hf : φ.denote ρ i f) (hg : φ.denote ρ i g) : f = g :=
    ((sat i f).mp hf).unique_l hZF.1 ((sat i g).mp hg)
  obtain ⟨D, hd⟩ := ZF.exists_functionalImage hZF φ ρ B ht unique
  obtain ⟨P, hp, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ ht (fun i _ => unique i)
    (fun i f hi hf => (hd f).mpr ⟨i, hi, hf⟩)
  exact ⟨P, hp.1, hp.2.1, fun i f => (ps i f).trans (and_congr_right fun _ => sat i f)⟩

theorem it_project_elementary_l {ω α T Q G B L A p H R q c C V d N e r i b X S : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d hZF ω α T Q G) (s : It_system_d B L Q G A p H R)
    (elementary : Di_elementary_d I ω L A p H R) (limit : Di_limit_d A p H R q C V)
    (model : Smdl_d I c C V) (he : Smap_d I ω c d C N e)
    (rs : ∀ a y, Rd_entry_d a y r ↔ M.mem a A ∧ ∃ z, Rd_entry_d a z q ∧ Rd_entry_d z y e)
    (hi : M.mem i B) (hb : Rd_entry_d i b Q) (mx : Smdl_d I b X S) :
    ∃ f, Smap_d I ω b d X N f ∧ It_project_d r i f := by
  obtain ⟨D, hq⟩ := h.family_l hZF
  obtain ⟨j, hj, js⟩ := it_stage_limit_l hZF hω h s elementary limit model hi hb mx
  obtain ⟨f, hf, fs⟩ := smap_comp_l I hZF hj he
  refine ⟨f, hf, hf.1.1.1.1, fun x y => ⟨?_, ?_⟩⟩
  · intro hxy
    obtain ⟨_, z, hxz, hzy⟩ := (fs x y).mp hxy
    obtain ⟨_, a, hp, haz⟩ := (js x z).mp hxz
    exact ⟨a, hp, (rs a y).mpr ⟨(limit.projection.bound_l haz).1, z, haz, hzy⟩⟩
  · rintro ⟨a, hp, hay⟩
    obtain ⟨ha, z, haz, hzy⟩ := (rs a y).mp hay
    have hx := (ep_at_read_l hq hb mx.1).mp (s.tags.at_l ha hp)
    exact (fs x y).mpr ⟨hx, z, (js x z).mpr ⟨hx, a, hp, haz⟩, hzy⟩

end YesMetaZFC.SetTheory.LargeCardinal
