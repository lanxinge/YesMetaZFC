import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedView
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativeRecord
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyHistory
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedNameSyntax

/-! # 完整原档案行及其当前共同图视图

外部行码保存产生时的结点、模型、存档、根图和工作复制图。
每行的原存档与数字图保持原值；当前模型中的事件经它自己的共同图解释。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

/-- 当前树的结点位置、三张原列及对应的工作复制历史。 -/
structure Tg_archive_frame_d (α : Type u) where
  o : α
  n : α
  Q : α
  G : α
  L : α
  H : α

def Tg_archive_row_d.link_d (f : Tg_archive_frame_d M.Domain) (s : Tg_archive_row_d M.Domain) : Prop :=
  M.mem s.i f.n ∧ Rd_entry_d s.i s.c f.Q ∧ It_map_d f.G f.o s.i s.p ∧
    Rd_entry_d s.i s.L f.L ∧ ∃ z Z α, Ic_at_d f.H s.i s.X s.A s.π z Z α

def Tg_archive_links_d (f : Tg_archive_frame_d M.Domain) (H : M.Domain) : Prop :=
  ∀ m r, ∀ s : Tg_archive_row_d M.Domain, M.PairMember I m r H → Rt_tuple_d s.values_d r → s.link_d f

/-- 结点、根图、支撑和复制行分别由真实延伸保持；原行码无需改变。 -/
theorem Tg_archive_links_d.extend_l {f f' : Tg_archive_frame_d M.Domain} {H : M.Domain}
    (old : Tg_archive_links_d I f H) (grow : M.MemberSubset f.n f'.n)
    (models : ∀ i c, Rd_entry_d i c f.Q → Rd_entry_d i c f'.Q)
    (maps : ∀ i p, M.mem i f.n → It_map_d f.G f.o i p → It_map_d f'.G f'.o i p)
    (levels : ∀ i L, Rd_entry_d i L f.L → Rd_entry_d i L f'.L)
    (rows : M.MemberSubset f.H f'.H) : Tg_archive_links_d I f' H := by
  intro m r s entry code
  obtain ⟨hi,node,root,active,z,Z,α,r,⟨p,pair,hp⟩,cell⟩ := old m r s entry code
  exact ⟨grow s.i hi,models _ _ node,maps _ _ hi root,levels _ _ active,
    z,Z,α,r,⟨p,pair,rows p hp⟩,cell⟩

/-- 实际追加的13项行码唯一确定本次原行。 -/
theorem Tg_archive_links_d.push_l {f : Tg_archive_frame_d M.Domain} {H H' m r : M.Domain}
    {s : Tg_archive_row_d M.Domain} (old : Tg_archive_links_d I f H)
    (code : Rt_tuple_d s.values_d r) (link : s.link_d f)
    (entries : ∀ l t, M.PairMember I l t H' ↔ M.PairMember I l t H ∨ l = m ∧ t = r) :
    Tg_archive_links_d I f H' := by
  intro l t a ht ca
  rcases (entries l t).mp ht with ht | ⟨rfl,rfl⟩
  · exact old l t a ht ca
  · have same : a = s := Tg_archive_row_d.eq_l (rt_tuple_inj_l ca code)
    exact same.symm ▸ link

def Tg_archive_entry_d (Ω γ Bγ C₀ N S B σ w C c e a b z h m r : M.Domain) : Prop :=
  ∃ s : Tg_archive_row_d M.Domain, Rt_tuple_d s.values_d r ∧
    Smdl_d I s.c s.X s.R ∧ Tg_saved_d I s.w s.X s.R s.η s.C s.L s.U s.q ∧
    (∃ z₀, Rr_layer_d I Ω s.X s.R s.w z₀) ∧
    Tg_basis_d I γ Bγ C₀ s.w s.X s.R s.C s.p ∧
    ∃ l φ V Γ g, Ic_agree_d I s.X s.R s.A s.π N S B σ s.L l φ s.U V Γ g ∧
      Tg_saved_view_d I s.X s.R s.w s.U s.q γ g N S w C c e a b z m h

def Tg_archive_views_d (Ω γ Bγ C₀ H N S B σ w C c e a b z h : M.Domain) : Prop :=
  ∀ m r, M.PairMember I m r H → Tg_archive_entry_d I Ω γ Bγ C₀ N S B σ w C c e a b z h m r

end YesMetaZFC.SetTheory.LargeCardinal
