import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Model
import YesMetaZFC.Model.SetTheory.Internal.TransitiveStructure

/-! # 指定约化幂商证书的绝对性

投影的全定义性提供每个类的源内代表。反向识别任意背景等价类时，
直接与该投影值作外延比较，不假设源具有全幂集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hKP : M.Models KP) {Z : M.Domain}
  (hZ : M.TransitiveSet Z) (nz : Nonempty {x // M.mem x Z})
  (pair : ∀ a b, M.mem a Z → M.mem b Z → ∃ p, M.mem p Z ∧ Pair_d M p a b)
include hKP hZ
local notation "N" => rt_model_l Z nz
local notation "I" => kp_pair_l hKP
local notation "J" => rt_pair_l hZ nz (And.left hKP) pair

theorem rt_rp_eq_l (Q U f g : (N).Domain) :
    Rp_eq_d Q U f g ↔ Rp_eq_d Q.val U.val f.val g.val := by
  let ρ : Env N 4 := ⟨Fin.cases g (Fin.cases f (Fin.cases U (fun _ => Q))), fun _ => Q⟩
  exact (rp_eq_sat_l (rt_model_ext_l hKP.1 hZ nz) ρ (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
    ((rt_model_delta_l hZ nz (rp_eq_delta_l ..) ρ).trans (rp_eq_sat_l hKP.1 ..))

theorem rt_rp_class_l (Q U G f B : (N).Domain) :
    Rp_class_d Q U G f B ↔ Rp_class_d Q.val U.val G.val f.val B.val := by
  constructor
  · intro h g
    constructor
    · intro hg
      obtain ⟨hG, he⟩ := (h ⟨g, hZ B.val B.property g hg⟩).mp hg
      exact ⟨hG, (rt_rp_eq_l hKP hZ nz ..).mp he⟩
    · rintro ⟨hg, he⟩
      exact (h ⟨g, hZ G.val G.property g hg⟩).mpr ⟨hg, (rt_rp_eq_l hKP hZ nz ..).mpr he⟩
  · intro h g
    exact (h g.val).trans (and_congr Iff.rfl (rt_rp_eq_l hKP hZ nz ..).symm)

theorem rt_rp_map_l (D Q U G p C : (N).Domain) :
    Rp_map_d J D Q U G p C ↔ Rp_map_d I D.val Q.val U.val G.val p.val C.val := by
  have fn := rt_function_from_l hZ nz hKP.1 (KP.exists_pair hKP) pair p G C
  have ran := rt_range_l hZ nz hKP.1 (KP.exists_pair hKP) pair C p
  constructor
  · intro h
    have proj := fn.mp h.projection
    have cls (f B : (N).Domain) := (rt_entry_l hZ nz hKP.1 f B p).symm.trans
      ((h.classes f B).trans (and_congr Iff.rfl (rt_rp_class_l hKP hZ nz Q U G f B)))
    refine ⟨fun f hf => (rt_fn_l hZ nz hKP.1 D Q ⟨f, hZ G.val G.property f hf⟩).mp
      (h.functions _ hf), proj, ran.mp h.range, fun f B => ⟨?_, ?_⟩⟩
    · intro hfB
      have mem := rd_entry_transitive_l hZ p.property hfB
      exact (cls ⟨f, mem.1⟩ ⟨B, mem.2⟩).mp hfB
    · rintro ⟨hf, hb⟩
      obtain ⟨B', hB', hfB'⟩ := proj.2.2 f hf
      have old := ((cls ⟨f, hZ G.val G.property f hf⟩ ⟨B', hZ C.val C.property B' hB'⟩).mp hfB').2
      have eq := hKP.1.eq_of_same_members B B' (fun g => (hb g).trans (old g).symm)
      exact eq.symm ▸ hfB'
  · intro h
    refine ⟨fun f hf => (rt_fn_l hZ nz hKP.1 ..).mpr (h.functions f.val hf),
      fn.mpr h.projection, ran.mpr h.range, fun f B => ?_⟩
    exact (rt_entry_l hZ nz hKP.1 f B p).trans
      ((h.classes f.val B.val).trans (and_congr Iff.rfl (rt_rp_class_l hKP hZ nz Q U G f B).symm))

theorem rt_rp_rel_l (Q U R f g : (N).Domain) :
    Rp_rel_d J Q U R f g ↔ Rp_rel_d I Q.val U.val R.val f.val g.val := by
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A.val, hA, fun i hi => ?_⟩
    obtain ⟨x, hx, y, hy, hix, hiy, hxy⟩ := h ⟨i, hZ A.val A.property i hi⟩ hi
    exact ⟨x.val, hx, y.val, hy, (rt_entry_l hZ nz hKP.1 ..).mp hix,
      (rt_entry_l hZ nz hKP.1 ..).mp hiy, (rt_entry_l hZ nz hKP.1 ..).mp hxy⟩
  · rintro ⟨A, hA, h⟩
    refine ⟨⟨A, hZ U.val U.property A hA⟩, hA, fun i hi => ?_⟩
    obtain ⟨x, hx, y, hy, hix, hiy, hxy⟩ := h i.val hi
    exact ⟨⟨x, hZ Q.val Q.property x hx⟩, hx, ⟨y, hZ Q.val Q.property y hy⟩, hy,
      (rt_entry_l hZ nz hKP.1 ..).mpr hix, (rt_entry_l hZ nz hKP.1 ..).mpr hiy,
      (rt_entry_l hZ nz hKP.1 ..).mpr hxy⟩

theorem rt_rp_model_l (D Q U R c G p C T : (N).Domain) :
    Rp_model_d J D Q U R c G p C T ↔ Rp_model_d I D.val Q.val U.val R.val c.val G.val p.val C.val T.val := by
  constructor
  · intro h
    refine ⟨(rt_rp_map_l hKP hZ nz pair ..).mp h.map, (rt_smdl_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mp h.code, ?_⟩
    intro f g B E hf hg
    have fb := rd_entry_transitive_l hZ p.property hf
    have ge := rd_entry_transitive_l hZ p.property hg
    exact (rt_entry_l hZ nz hKP.1 ⟨B, fb.2⟩ ⟨E, ge.2⟩ T).symm.trans
      ((h.relation ⟨f, fb.1⟩ ⟨g, ge.1⟩ ⟨B, fb.2⟩ ⟨E, ge.2⟩ ((rt_entry_l hZ nz hKP.1 ..).mpr hf)
        ((rt_entry_l hZ nz hKP.1 ..).mpr hg)).trans (rt_rp_rel_l hKP hZ nz pair ..))
  · intro h
    refine ⟨(rt_rp_map_l hKP hZ nz pair ..).mpr h.map, (rt_smdl_l hKP.1 (KP.exists_pair hKP) hZ nz pair ..).mpr h.code, ?_⟩
    intro f g B E hf hg
    exact (rt_entry_l hZ nz hKP.1 B E T).trans
      ((h.relation f.val g.val B.val E.val ((rt_entry_l hZ nz hKP.1 ..).mp hf)
        ((rt_entry_l hZ nz hKP.1 ..).mp hg)).trans (rt_rp_rel_l hKP hZ nz pair ..).symm)

end YesMetaZFC.SetTheory.Internal
