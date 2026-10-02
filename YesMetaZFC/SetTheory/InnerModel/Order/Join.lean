import YesMetaZFC.SetTheory.InnerModel.Order.State
import YesMetaZFC.SetTheory.InnerModel.Jensen.Operator

/-! # 配对状态族的坐标并

两个坐标分别取并，再组成一个新状态。非对成员的投影为空集，因此不改变并。
此算子在任意输入上总且单值，为零与极限阶段提供共同定义。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Rp_union_d (i : Bool) (X U : M.Domain) : Prop :=
  ∀ x, M.mem x U ↔ ∃ p, M.mem p X ∧ ∃ A, Rp_proj_d i p A ∧ M.mem x A
def rp_union_s (i : Bool) : S1_binary 0 := (S1_binary.of_delta0 (rp_proj_s i)).image.comp (rd_unary_s .union)

theorem rp_union_sat_l (hKP : M.Models KP) (ρ : Env M 0) (i : Bool) (X U : M.Domain) :
    (rp_union_s i).schema.denote ρ X U ↔ Rp_union_d i X U := by
  have image D := S1_binary.image_sat_l hKP (S1_binary.of_delta0 (rp_proj_s i)) ρ X D
    (fun p _ => (rp_proj_total_l hKP i p).imp fun x hx =>
      (S1_binary.of_delta0_sat_l _ ρ p x).mpr ((rp_proj_schema_l hKP.1 ρ i p x).mpr hx))
    (fun _ _ _ _ h g => rp_proj_unique_l hKP.1
      ((rp_proj_schema_l hKP.1 ..).mp ((S1_binary.of_delta0_sat_l ..).mp h))
      ((rp_proj_schema_l hKP.1 ..).mp ((S1_binary.of_delta0_sat_l ..).mp g)))
  simp only [rp_union_s, S1_binary.comp_sat_l hKP, image, S1_binary.of_delta0_sat_l,
    rp_proj_schema_l hKP.1, rd_unary_sat_l hKP]
  constructor
  · rintro ⟨D, hd, hu⟩ x
    rw [hu x]
    change (∃ A, M.mem A D ∧ M.mem x A) ↔ _
    exact ⟨fun ⟨A, hA, hx⟩ => ((hd A).mp hA).elim (fun p hp => ⟨p, hp.1, A, hp.2, hx⟩),
      fun ⟨p, hp, A, ha, hx⟩ => ⟨A, (hd A).mpr ⟨p, hp, ha⟩, hx⟩⟩
  · intro hu
    obtain ⟨D, hd⟩ := KP.d0_image_l hKP (rp_proj_s i) ρ X
      (fun p _ => (rp_proj_total_l hKP i p).imp fun x hx => (rp_proj_schema_l hKP.1 ρ i p x).mpr hx)
      (fun _ _ _ _ h g => rp_proj_unique_l hKP.1 ((rp_proj_schema_l hKP.1 ..).mp h) ((rp_proj_schema_l hKP.1 ..).mp g))
    have hd A : M.mem A D ↔ ∃ p, M.mem p X ∧ Rp_proj_d i p A :=
      (hd A).trans (exists_congr fun p => and_congr_right fun _ => rp_proj_schema_l hKP.1 ρ i p A)
    refine ⟨D, hd, fun x => (hu x).trans ?_⟩
    exact ⟨fun ⟨p, hp, A, ha, hx⟩ => ⟨A, (hd A).mpr ⟨p, hp, ha⟩, hx⟩,
      fun ⟨A, hA, hx⟩ => ((hd A).mp hA).elim (fun p hp => ⟨p, hp.1, A, hp.2, hx⟩)⟩

theorem rp_union_exists_l (hKP : M.Models KP) (i : Bool) (X : M.Domain) : ∃ U, Rp_union_d i X U := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => X⟩
  obtain ⟨D, hd⟩ := KP.d0_image_l hKP (rp_proj_s i) ρ X
    (fun p _ => (rp_proj_total_l hKP i p).imp fun x hx => (rp_proj_schema_l hKP.1 ρ i p x).mpr hx)
    (fun _ _ _ _ h g => rp_proj_unique_l hKP.1 ((rp_proj_schema_l hKP.1 ..).mp h) ((rp_proj_schema_l hKP.1 ..).mp g))
  obtain ⟨U, hu⟩ := rd_fun_exists_l hKP .union D D D
  refine ⟨U, fun x => (hu x).trans ?_⟩
  constructor
  · rintro ⟨A, hA, hx⟩
    obtain ⟨p, hp, ha⟩ := (hd A).mp hA
    exact ⟨p, hp, A, (rp_proj_schema_l hKP.1 ρ i p A).mp ha, hx⟩
  · rintro ⟨p, hp, A, ha, hx⟩
    exact ⟨A, (hd A).mpr ⟨p, hp, (rp_proj_schema_l hKP.1 ρ i p A).mpr ha⟩, hx⟩

theorem rp_union_unique_l (hE : Extensional M) {i X U V} (h : Rp_union_d (M := M) i X U)
    (g : Rp_union_d i X V) : U = V := hE.eq_of_same_members _ _ fun x => (h x).trans (g x).symm

theorem rp_union_entry_l {i : Bool} {X U : M.Domain} (h : Rp_union_d i X U) (x : M.Domain) :
    M.mem x U ↔ ∃ A R, Rd_entry_d A R X ∧ M.mem x (if i then R else A) := by
  rw [h x]
  constructor
  · rintro ⟨p, hp, A, ⟨R, hr⟩ | ⟨_, he⟩, hx⟩
    · cases i
      · exact ⟨A, R, ⟨p, hr, hp⟩, hx⟩
      · exact ⟨R, A, ⟨p, hr, hp⟩, hx⟩
    · exact (he x hx).elim
  · rintro ⟨A, R, ⟨p, hp, hpX⟩, hx⟩
    cases i
    · exact ⟨p, hpX, A, Or.inl ⟨R, hp⟩, hx⟩
    · exact ⟨p, hpX, R, Or.inl ⟨A, hp⟩, hx⟩

def Rw_join_d (X p : M.Domain) : Prop := ∃ U R, Rp_union_d false X U ∧ Rp_union_d true X R ∧ KPair_d M p U R
def rw_join_s : S1_binary 0 := (rp_union_s false).pair (rp_union_s true)
theorem rw_join_sat_l (hKP : M.Models KP) (ρ : Env M 0) (X p : M.Domain) :
    rw_join_s.schema.denote ρ X p ↔ Rw_join_d X p := by
  simp only [rw_join_s, S1_binary.pair_sat_l hKP, rp_union_sat_l hKP]; rfl
theorem rw_join_exists_l (hKP : M.Models KP) (X : M.Domain) : ∃ p, Rw_join_d X p := by
  obtain ⟨U, hu⟩ := rp_union_exists_l hKP false X
  obtain ⟨R, hr⟩ := rp_union_exists_l hKP true X
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total U R
  exact ⟨p, U, R, hu, hr, hp⟩
theorem rw_join_unique_l (hE : Extensional M) {X p q} (h : Rw_join_d (M := M) X p) (g : Rw_join_d X q) : p = q := by
  obtain ⟨U, R, hu, hr, hp⟩ := h
  obtain ⟨V, S, hv, hs, hq⟩ := g
  have he := rp_union_unique_l hE hu hv; subst V
  have he := rp_union_unique_l hE hr hs; subst S
  exact kpair_unique_l M hE hp hq

theorem Rw_join_d.coordinates_l {X p U R : M.Domain} (h : Rw_join_d X p) (hp : KPair_d M p U R) :
    Rp_union_d false X U ∧ Rp_union_d true X R := by
  obtain ⟨A, B, ha, hb, hp'⟩ := h
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M hp' hp
  exact ⟨ha, hb⟩

theorem rw_join_entry_l {X R : M.Domain} (h : Rp_union_d true X R) (x y : M.Domain) :
    Rd_entry_d x y R ↔ ∃ A S, Rd_entry_d A S X ∧ Rd_entry_d x y S := by
  constructor
  · rintro ⟨p, hp, hpR⟩
    obtain ⟨A, S, ha, hpS⟩ := (rp_union_entry_l h p).mp hpR
    exact ⟨A, S, ha, p, hp, hpS⟩
  · rintro ⟨A, S, ha, p, hp, hpS⟩
    exact ⟨p, hp, (rp_union_entry_l h p).mpr ⟨A, S, ha, hpS⟩⟩

end YesMetaZFC.SetTheory.InnerModel
