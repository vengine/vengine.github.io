#include "render_system.h"
#include <xhnSTL/xhn_exception.hpp>
#include <pthread.h>
#include <xhnSTL/emem.h>
#include <xhnSTL/elog.h>
#include "shader_log.h"
#include "float_base.h"
#include <xhnSTL/tree.h>
#include "vertex_declaration.h"
#include "pass.h"
#include "compositor_pass.h"
#include "image.h"
#include "png_load.h"
#include "texture_copy_renderer.h"

#include <xhnSTL/xhn_static_string.hpp>
#include <xhnSTL/xhn_set.hpp>

#include "font_renderer.h"
#include "gl_lock.h"
#include "debug.h"

#include "render_buffer_manager.h"
#include <xhnSTL/xhn_file_stream.hpp>

#include "robot_thread.h"

#include "forward_light_manager.h"
#include "depth_texture_renderer.h"
#include "blurry_texture_renderer.h"
#include "forward_renderer.h"

#include "scene_manager.h"

#include "frame_buffer_manager.h"

#include "material_prototype.h"
#include "robot.h"
namespace VEngine {
using namespace VType;

class VPerformanceMeasurement : public RefObject
{
    friend class xhn::SmartPtr<VPerformanceMeasurement>;
public:
    TimeCheckpoint m_tc;
    xhn::string m_unit;
    VPerformanceMeasurement(xhn::string unit)
    : m_unit(unit)
    {
        m_tc = TimeCheckpoint::Tick();
    }
private:
    ~VPerformanceMeasurement()
    {
        VTime t;
        TimeCheckpoint::Tock(m_tc, t);
        elog("%s: = %f ms", m_unit.c_str(), t.GetMicrosecond());
        elog("%s:", m_unit.c_str());
    }
};

typedef xhn::SmartPtr<VPerformanceMeasurement> VPerformanceMeasurementPtr;

xhn::static_string BaseGroupName("BaseGroup");
xhn::static_string TextureGroupName("Texture");
xhn::static_string GUIConfigGroupName("GUIConfig");
xhn::static_string AnimationConfigGroupName("AnimationConfig");
xhn::static_string InternalTextureGroupName("InternalTexture");
xhn::static_string FontGroupName("Font");
xhn::static_string MaterialPrototypeGroupName("MaterialPrototype");
xhn::static_string MaterialInstanceGroupName("MaterialInstance");
xhn::static_string MeshGroupName("Mesh");
xhn::static_string SkinGroupName("Skin");
xhn::static_string AnimationGroupName("Animation");

VTexture2DPtr _create_texture_from_file(VRenderSystem* renderSys, FileStream file_stream)
{
    Image img = png_load(file_stream);

    if (to_ptr(img))
    {
        euint32 h = Image_get_num_rows(img);
        euint32 w = Image_get_row_width(img);
        PixelFormat fmt = Image_get_pixel_format(img);
		VTexture2DPtr tex = VTexture2DGallery::Get(renderSys)->RegisterArtistTexture();
        vptr pxls = Image_get_row(img, 0);
        tex->LoadFromMem(pxls, fmt, w, h, true);

        Image_delete(img);
        
        return tex;
    }

    return NULL;
}

VTexture2DPtr _create_texture_from_file(VRenderSystem* renderSys, const char* _file_name)
{
    ///FILE* file_stream = SafeFOpen(_file_name, "rb");
    FileStream file_stream = IFileStream::LoadFromFilename(_file_name);
	return _create_texture_from_file(renderSys, file_stream);
}

bool VRenderSystem::IsInited()
{
    return m_render_system_inited;
}

///==========================================================================///
///  渲染系统初始化和结束                                                       ///
///==========================================================================///
VRenderSystem::VRenderSystem()
: m_ComposingStickManager(nullptr)
, m_GLLock(nullptr)
, m_GUICurveDataBase(nullptr)
, m_InterfaceRenderList(nullptr)
, m_ResourceSystem(nullptr)
, m_RobotManager(nullptr)
, m_RobotThreadManager(nullptr)
, m_FrameBufferManager(nullptr)
, m_SpriteEventHub(nullptr)
, m_Texture2DGallery(nullptr)
, m_TextureCubeGallery(nullptr)
, m_TextureCopyRenderer(nullptr)
, m_SceneManager(nullptr)
, m_BaseFrameBuffer(nullptr)
///
, m_cursor(NULL)
, m_max_texture_units(0)
///
, m_vidCount(0)
, m_mesh_count(0)
, m_forceUpdateCount(0)
, m_event_buffer(NULL)
, m_log_level(SHADER_LOG)
///
, m_entryPoint(0)
///
, m_vtx_dec_set(NULL)
, m_compositor_pass_map(NULL)
, m_render_buffer_manager(NULL)
, m_render_system_inited(false)
///
#ifdef USE_LOG_SYSTEM
, m_std_pass_log_file(NULL)
, m_lighting_pass_log_file(NULL)
, m_post_pass_log_file(NULL)
, m_material_pass_log_file(NULL)
#endif
{
    m_mainRendererChain = VNEW VRendererChain(this);
    m_mainRendererChain->Init();
}
static VTexture2DPtr s_tempDirectionShadowTexture;
static VTexture2DPtr s_tempSpotShadowTexture;
static VTexture2DPtr s_pointTempShadowTexture0;
static VTexture2DPtr s_pointTempShadowTexture1;
static VTexture2DPtr s_pointTempShadowTexture2;
static VTexture2DPtr s_pointTempShadowTexture3;
static VTexture2DPtr s_pointTempShadowTexture4;
static VTexture2DPtr s_pointTempShadowTexture5;

PushMainFunctionProc VRenderSystem::Init(VRenderRobot* renderRobot)
{
    ERROR_PROC;
    
    StartUp();

    m_vtx_dec_set = VNEW VertexDeclSet;
    m_blur_pass_map = VNEW VertexDeclToPassMap;
    m_single_texture_pass_map = VNEW VertexDeclToPassMap;
    m_compositor_pass_map = VNEW CompPassDeclToPassMap;
    
	VNEW VResourceSystem(this);
	VTexture2DGallery::Init(this);
    VTextureCubeGallery::Init(this);
    FrameBufferManager::Init(this);
    VTextureCopyRenderer::Init(this, renderRobot);
    VSceneManager::Init(this);
	
	VResourceGroup* grp = VResourceSystem::Get(this)->GetResourceGroup(BaseGroupName);

    xhn::vector<xhn::wstring> resDirs;
    xhn::vector<xhn::wstring> fontDirs;
    xhn::file_manager::get()->get_resource_dirs(resDirs);
    xhn::file_manager::get()->get_system_font_dirs(fontDirs);
    xhn::vector<xhn::wstring>::iterator iter = resDirs.begin();
    xhn::vector<xhn::wstring>::iterator end = resDirs.end();
    for (; iter != end; iter++) {
        xhn::wstring& resourceDir = *iter;
        xhn::Utf8 utf8ResourceDir(resourceDir.c_str());
        grp->RegisterResourceDirectory(((xhn::string)utf8ResourceDir).c_str(), Public);
    }

	VResourceSystem::Get(this)->NewResourceGroup(TextureGroupName, BaseGroupName, Public);
	VResourceSystem::Get(this)->NewResourceGroup(GUIConfigGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(AnimationConfigGroupName, BaseGroupName, Public);
	VResourceSystem::Get(this)->NewResourceGroup(InternalTextureGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(FontGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(MaterialPrototypeGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(MaterialInstanceGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(MeshGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(SkinGroupName, BaseGroupName, Public);
    VResourceSystem::Get(this)->NewResourceGroup(AnimationGroupName, BaseGroupName, Public);
	
	grp = VResourceSystem::Get(this)->GetResourceGroup(TextureGroupName);
    grp->SetFileImpl(VNEW LazyFileImpl);
	grp->RegisterResourceImplement(VNEW VTexture2DImplement(this));
	grp->RegisterResourceImplement(VNEW DefaultTexture2DImplement(this));
    grp->RegisterResourceImplement(VNEW VTextureCubeImplement(this));
    grp->RegisterResourceImplement(VNEW DefaultTextureCubeImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(GUIConfigGroupName);
	grp->RegisterResourceImplement(VNEW VXMLImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(AnimationConfigGroupName);
    grp->RegisterResourceImplement(VNEW VXMLImplement(this));

	grp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
	grp->SetFileImpl(VNEW EmptyFileImpl);
	grp->RegisterResourceImplement(VNEW InternalTexture2DImplement(this));
    grp->RegisterResourceImplement(VNEW InternalTextureCubeImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(FontGroupName);
    grp->RegisterResourceImplement(VNEW VFontImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(MaterialPrototypeGroupName);
    grp->RegisterResourceImplement(VNEW VMaterialPrototypeImplement(this));
    grp->RegisterResourceImplement(VNEW InvalidMaterialPrototypeImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(MaterialInstanceGroupName);
    grp->RegisterResourceImplement(VNEW VMaterialInstanceImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(SkinGroupName);
    grp->RegisterResourceImplement(VNEW VSkinImplement(this));
    
    grp = VResourceSystem::Get(this)->GetResourceGroup(AnimationGroupName);
    grp->RegisterResourceImplement(VNEW VAnimationImplement(this));

	m_render_buffer_manager = VNEW VRenderBufferManager(this);
    
    VComposingStickManager::Init(this);
    MemBarrier;
    m_render_system_inited = true;
    
    m_forwardLightManager = VNEW VForwardLightManager(this);
    {
        VLightManagerInstance inst = m_forwardLightManager->GetInstance();
        inst->Init();
    }
    m_directionShadowRendererChain = VNEW VRendererChain(this);
    m_spotShadowRendererChain = VNEW VRendererChain(this);
    m_pointShadowRendererChain = VNEW VRendererChain(this);
    m_directionShadowRendererChain->Init();
    m_spotShadowRendererChain->Init();
    m_pointShadowRendererChain->Init();
    m_directionShadowRendererChain->SetLightManager(m_forwardLightManager);
    m_spotShadowRendererChain->SetLightManager(m_forwardLightManager);
    m_pointShadowRendererChain->SetLightManager(m_forwardLightManager);
    

    auto addShadowTexture = [this](const xhn::static_string texName, euint32 textureSize, VTexture2DPtr& result) {
        result = VTexture2DGallery::Get(this)->RegisterInternalTexture(texName);
        VResourceGroup* grp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
        VTexture2DResource* res = VNEW VTexture2DResource(this, grp, result);
        grp->AddResource(texName, res);
        result->CreateEmptyTextureNoBuffered(RG32F, textureSize, textureSize);
    };
    addShadowTexture("DirectionShadowTempTexture2D", DEFAULT_DIRECTION_SHADOW_MAP_SIZE, s_tempDirectionShadowTexture);
    addShadowTexture("SpotShadowTempTexture2D", DEFAULT_SHADOW_MAP_SIZE, s_tempSpotShadowTexture);
    addShadowTexture("PointShadowTempTexture2D0", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture0);
    addShadowTexture("PointShadowTempTexture2D1", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture1);
    addShadowTexture("PointShadowTempTexture2D2", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture2);
    addShadowTexture("PointShadowTempTexture2D3", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture3);
    addShadowTexture("PointShadowTempTexture2D4", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture4);
    addShadowTexture("PointShadowTempTexture2D5", DEFAULT_SHADOW_MAP_SIZE, s_pointTempShadowTexture5);
    
    VDepthTextureRenderer* ddtr =
    VNEW VDepthTextureRenderer(this,
                               renderRobot,
                               "DirectionShadowRenderer",
                               "DirectionShadowTempTexture2D");
    VDepthTextureRenderer* sdtr =
    VNEW VDepthTextureRenderer(this,
                               renderRobot,
                               "SpotShadowRenderer",
                               "SpotShadowTempTexture2D");
    m_directionShadowRendererChain->AddRenderer(ddtr);
    m_directionShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                            renderRobot,
                                                                            "DirectionBlurryRenderer",
                                                                            "DirectionShadowTempTexture2D",
                                                                            ""));
    
    m_spotShadowRendererChain->AddRenderer(sdtr);
    m_spotShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                       renderRobot,
                                                                       "SpotBlurryRenderer",
                                                                       "SpotShadowTempTexture2D",
                                                                       ""));
    
    VDepthTextureRenderer* pdtr0 = nullptr;
    VDepthTextureRenderer* pdtr1 = nullptr;
    VDepthTextureRenderer* pdtr2 = nullptr;
    VDepthTextureRenderer* pdtr3 = nullptr;
    VDepthTextureRenderer* pdtr4 = nullptr;
    VDepthTextureRenderer* pdtr5 = nullptr;
    
    pdtr0 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer0",
                                       "PointShadowTempTexture2D0");
    pdtr1 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer1",
                                       "PointShadowTempTexture2D1");
    pdtr2 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer2",
                                       "PointShadowTempTexture2D2");
    pdtr3 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer3",
                                       "PointShadowTempTexture2D3");
    pdtr4 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer4",
                                       "PointShadowTempTexture2D4");
    pdtr5 = VNEW VDepthTextureRenderer(this,
                                       renderRobot,
                                       "PointShadowRenderer5",
                                       "PointShadowTempTexture2D5");
    
    pdtr0->m_isPointDepthTexture = true;
    pdtr1->m_isPointDepthTexture = true;
    pdtr2->m_isPointDepthTexture = true;
    pdtr3->m_isPointDepthTexture = true;
    pdtr4->m_isPointDepthTexture = true;
    pdtr5->m_isPointDepthTexture = true;

    m_pointShadowRendererChain->AddRenderer(pdtr0);
    m_pointShadowRendererChain->AddRenderer(pdtr1);
    m_pointShadowRendererChain->AddRenderer(pdtr2);
    m_pointShadowRendererChain->AddRenderer(pdtr3);
    m_pointShadowRendererChain->AddRenderer(pdtr4);
    m_pointShadowRendererChain->AddRenderer(pdtr5);
    
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer0", "PointShadowTempTexture2D0",
                                                                        ""));
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer1", "PointShadowTempTexture2D1",
                                                                        ""));
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer2", "PointShadowTempTexture2D2",
                                                                        ""));
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer3", "PointShadowTempTexture2D3",
                                                                        ""));
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer4", "PointShadowTempTexture2D4",
                                                                        ""));
    m_pointShadowRendererChain->AddRenderer(VNEW VBlurryTextureRenderer(this,
                                                                        renderRobot,
                                                                        "PointBlurryRenderer5", "PointShadowTempTexture2D5",
                                                                        ""));
    
    VMaterialPrototype::MaterialForCompileFailed = LoadMaterialPrototype("fail_material.vmp");
    
    return (PushMainFunctionProc)&VRenderSystem::PushDefaultMainFunction;
}

VRenderSystem::~VRenderSystem()
{
    delete m_vtx_dec_set;
    {
        CompPassDeclToPassMap::iterator iter = m_compositor_pass_map->begin();
        CompPassDeclToPassMap::iterator end = m_compositor_pass_map->end();
        for (; iter != end; iter++) {
            Mfree(iter->first);
        }
    }
    delete m_compositor_pass_map;
    
	delete VResourceSystem::Get(this);
	delete m_render_buffer_manager;
	VTexture2DGallery::Dest(this);
    VTextureCubeGallery::Dest(this);
    FrameBufferManager::Dest(this);
    VTextureCopyRenderer::Dest(this);
    VSceneManager::Dest(this);
}

void VRenderSystem::PushForwardKeyLights()
{
    VLightManagerInstance inst = m_forwardLightManager->GetInstance();
    VLightGroupPtr lightGroup = inst->GetKeyLightGroup();
    if (!lightGroup)
        return;
    {
        DirLightArray::iterator iter = lightGroup->m_dirLights.begin();
        DirLightArray::iterator end = lightGroup->m_dirLights.end();
        for (; iter != end; iter++) {
            VDirectionLightPtr dirLight = *iter;
            m_stack[m_stackPointer++] = (euint)dirLight.get();
        }
    }
    {
        SpotLightArray::iterator iter = lightGroup->m_spotLights.begin();
        SpotLightArray::iterator end = lightGroup->m_spotLights.end();
        for (; iter != end; iter++) {
            VSpotLightPtr spotLight = *iter;
            m_stack[m_stackPointer++] = (euint)spotLight.get();
        }
    }
    {
        PointLightArray::iterator iter = lightGroup->m_pointLights.begin();
        PointLightArray::iterator end = lightGroup->m_pointLights.end();
        for (; iter != end; iter++) {
            VPointLightPtr pointLight = *iter;
            m_stack[m_stackPointer++] = (euint)pointLight.get();
        }
    }
}

void VRenderSystem::GetLightTypeToReg0()
{
    m_reg0 = (euint)((VLight*)m_reg0)->GetType();
}
void VRenderSystem::GetDirectionShadowRendererChainToReg0()
{
    m_reg0 = (euint)m_directionShadowRendererChain.get();
}
void VRenderSystem::GetSpotShadowRendererChainToReg0()
{
    m_reg0 = (euint)m_spotShadowRendererChain.get();
}
void VRenderSystem::GetPointShadowRendererChainToReg0()
{
    m_reg0 = (euint)m_pointShadowRendererChain.get();
}
void VRenderSystem::GetShadowCameraToReg0(esint32 index)
{
    m_reg0 = (euint)((VLight*)m_reg0)->GetCamera((euint)index).get();
}
void VRenderSystem::GetShadowTextureNameToReg0(esint32 index)
{
    m_reg0 = (euint)((VLight*)m_reg0)->GetShadowTextureName((euint)index).c_str();
}
void VRenderSystem::GetDirectionShadowViewportToReg0()
{
    m_reg0 = (euint)m_forwardLightManager->GetDirectionShadowViewport().get();
}
void VRenderSystem::GetSpotShadowViewportToReg0()
{
    m_reg0 = (euint)m_forwardLightManager->GetSpotShadowViewport().get();
}
void VRenderSystem::GetPointShadowViewportToReg0()
{
    m_reg0 = (euint)m_forwardLightManager->GetPointShadowViewport().get();
}
void VRenderSystem::ClearRendererChainViewports()
{
    ((VRendererChain*)m_reg0)->ClearViewportStack();
}
void VRenderSystem::ClearRendererChainCameras()
{
    ((VRendererChain*)m_reg0)->ClearCameraStack();
}
void VRenderSystem::PushCameraToRendererChain(esint32 offs)
{
    euint data = m_stack[m_backupStackPointer + offs];
    ((VRendererChain*)m_reg0)->PushCamera((VCamera*)data);
}
void VRenderSystem::PushViewportToRendererChain(esint32 offs)
{
    euint data = m_stack[m_backupStackPointer + offs];
    ((VRendererChain*)m_reg0)->PushViewport((VViewport*)data);
}
void VRenderSystem::SetNormalShadowTextureToRendererChain(esint32 offs)
{
    euint data = m_stack[m_backupStackPointer + offs];
    ((VRendererChain*)m_reg0)->SetOutputTexture(xhn::static_string((const char*)data), T2D);
}
void VRenderSystem::SetCubeShadowTextureToRendererChain(esint32 offs)
{
    euint data = m_stack[m_backupStackPointer + offs];
    ((VRendererChain*)m_reg0)->SetOutputTexture(xhn::static_string((const char*)data), TCube);
}
void VRenderSystem::GetNumForwardKeyLightsToReg0()
{
    VLightManagerInstance inst = m_forwardLightManager->GetInstance();
    VLightGroupPtr mainLightGroup = inst->GetKeyLightGroup();
    if (mainLightGroup) {
        m_reg0 = (euint)(mainLightGroup->m_dirLights.size() + mainLightGroup->m_pointLights.size() + mainLightGroup->m_spotLights.size());
    }
    else {
        m_reg0 = 0;
    }
}
void VRenderSystem::GetMainRendererChainToReg0()
{
    m_reg0 = (euint)m_mainRendererChain.get();
}

void VRenderSystem::PushRenderShadowFunction()
{
    /// 这函数参数有两组，一组是所有的前向关键灯光
    /// 另一组是灯光数目，这是个int值
    const esint32 RemainderLights = 0;
    const esint32 LightIndex = 1;
    const esint32 Light = 2;
    const esint32 RendererChain = 3;
    const esint32 ShadowCamera = 4;
    const esint32 ShadowTextureName = 5;
    const esint32 DirectionShadowViewport = 6;
    const esint32 SpotShadowViewport = 7;
    const esint32 PointShadowViewport = 8;
    
    PushCommand({ALLOC_IMME, 16}, __FILE__, __LINE__);
    ///PushCommand({MOV_MEM_TO_REG0, GetLastArgOffs()}, __FILE__, __LINE__);
    PushCommand({MOV_IMME_TO_REG1, GetLastArgOffs()}, __FILE__, __LINE__);
    PushCommand({DEC_REG1, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG1_TO_MEM, LightIndex}, __FILE__, __LINE__);
    
    PushCommand({GET_DIR_SDW_VIEW_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, DirectionShadowViewport}, __FILE__, __LINE__);
    
    PushCommand({GET_SPT_SDW_VIEW_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, SpotShadowViewport}, __FILE__, __LINE__);
    
    PushCommand({GET_PT_SDW_VIEW_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, PointShadowViewport}, __FILE__, __LINE__);
    
    PushCommand({MOV_MEM_TO_REG0, GetLastArgOffs()}, __FILE__, __LINE__);
    ///
    
    esint32 loop =
    PushCommand({MOV_REG0_TO_MEM, RemainderLights}, __FILE__, __LINE__);
    ///
    esint32 branch0 = 0;
    esint32 jumpOut0 = 0;
    esint32 nextElseIf0 = 0;
    esint32 branch1 = 0;
    esint32 jumpOut1 = 0;
    esint32 nextElseIf1 = 0;
    esint32 branch2 = 0;
    /// if (GetLightType() == VLight::SpotLight)
    {
        PushCommand({MOV_MEM_TO_REG0, LightIndex}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_IDX_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, Light}, __FILE__, __LINE__);
        
        /// 用 reg0 指向的栈空间作为灯光指针，取得该指针的type存到 reg0 里
        PushCommand({GET_LIGHT_TYPE_TO_REG0, 0}, __FILE__, __LINE__);
        /// 准备进行比较
        PushCommand({MOV_REG0_TO_REG1, 0}, __FILE__, __LINE__);
        PushCommand({MOV_IMME_TO_REG2, (esint32)VLight::SpotLight}, __FILE__, __LINE__);
        
        PushCommand({SUB_REG0_ASS_REG1_REG2, 0}, __FILE__, __LINE__);
        branch0 =
        PushCommand({JUMP_IF_NON_ZERO, 0}, __FILE__, __LINE__);
        
        PushCommand({GET_SPT_SDW_RDR_CHN_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, RendererChain}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        /// 平行光只有一个摄像机
        PushCommand({GET_SDW_CAM_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_TEX_NAME_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_CAMS, 0}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_VIEWS, 0}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({PUSH_VIEW_TO_RDR_CHN, SpotShadowViewport}, __FILE__, __LINE__);
        PushCommand({SET_NOR_SDW_TEX_TO_RDR_CHN, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({RENDER, RendererChain}, __FILE__, __LINE__);
        jumpOut0 =
        PushCommand({LJUMP, 0}, __FILE__, __LINE__);
    }
    /// else if (GetLightType() == VLight::DirectionLight)
    {
        nextElseIf0 =
        PushCommand({MOV_MEM_TO_REG0, LightIndex}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_IDX_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, Light}, __FILE__, __LINE__);
        
        /// 用 reg0 指向的栈空间作为灯光指针，取得该指针的type存到 reg0 里
        PushCommand({GET_LIGHT_TYPE_TO_REG0, 0}, __FILE__, __LINE__);
        /// 准备进行比较
        PushCommand({MOV_REG0_TO_REG1, 0}, __FILE__, __LINE__);
        PushCommand({MOV_IMME_TO_REG2, (esint32)VLight::DirectionLight}, __FILE__, __LINE__);
        
        PushCommand({SUB_REG0_ASS_REG1_REG2, 0}, __FILE__, __LINE__);
        branch1 =
        PushCommand({JUMP_IF_NON_ZERO, 0}, __FILE__, __LINE__);
        
        PushCommand({GET_DIR_SDW_RDR_CHN_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, RendererChain}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        /// 平行光只有一个摄像机
        PushCommand({GET_SDW_CAM_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_TEX_NAME_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_CAMS, 0}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_VIEWS, 0}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({PUSH_VIEW_TO_RDR_CHN, DirectionShadowViewport}, __FILE__, __LINE__);
        PushCommand({SET_NOR_SDW_TEX_TO_RDR_CHN, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({RENDER, RendererChain}, __FILE__, __LINE__);
        jumpOut1 =
        PushCommand({LJUMP, 0}, __FILE__, __LINE__);
    }
    /// else if (GetLightType() == VLight::PointLight)
    {
        nextElseIf1 =
        PushCommand({MOV_MEM_TO_REG0, LightIndex}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_IDX_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, Light}, __FILE__, __LINE__);
        
        /// 用 reg0 指向的栈空间作为灯光指针，取得该指针的type存到 reg0 里
        PushCommand({GET_LIGHT_TYPE_TO_REG0, 0}, __FILE__, __LINE__);
        /// 准备进行比较
        PushCommand({MOV_REG0_TO_REG1, 0}, __FILE__, __LINE__);
        PushCommand({MOV_IMME_TO_REG2, (esint32)VLight::PointLight}, __FILE__, __LINE__);
        
        PushCommand({SUB_REG0_ASS_REG1_REG2, 0}, __FILE__, __LINE__);
        branch2 =
        PushCommand({JUMP_IF_NON_ZERO, 0}, __FILE__, __LINE__);
        
        PushCommand({GET_PT_SDW_RDR_CHN_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, RendererChain}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_CAMS, 0}, __FILE__, __LINE__);
        PushCommand({CLEAR_RDR_CHN_VIEWS, 0}, __FILE__, __LINE__);
        
        /// 点光源有六个摄像机
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({PUSH_VIEW_TO_RDR_CHN, PointShadowViewport}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 1}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 2}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 3}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 4}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_CAM_TO_REG0, 5}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowCamera}, __FILE__, __LINE__);
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({PUSH_CAM_TO_RDR_CHN, ShadowCamera}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, Light}, __FILE__, __LINE__);
        PushCommand({GET_SDW_TEX_NAME_TO_REG0, 0}, __FILE__, __LINE__);
        PushCommand({MOV_REG0_TO_MEM, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({MOV_MEM_TO_REG0, RendererChain}, __FILE__, __LINE__);
        PushCommand({SET_CUBE_SDW_TEX_TO_RDR_CHN, ShadowTextureName}, __FILE__, __LINE__);
        
        PushCommand({RENDER, RendererChain}, __FILE__, __LINE__);
    }
    
    esint32 outOfBranch =
    PushCommand({MOV_MEM_TO_REG1, LightIndex}, __FILE__, __LINE__);
    PushCommand({DEC_REG1, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG1_TO_MEM, LightIndex}, __FILE__, __LINE__);
    ///
    
    PushCommand({MOV_MEM_TO_REG0, RemainderLights}, __FILE__, __LINE__);
    
    ///
    GetCommand(branch0).offs = nextElseIf0;
    GetCommand(branch1).offs = nextElseIf1;
    GetCommand(branch2).offs = outOfBranch;
    GetCommand(jumpOut0).offs = outOfBranch;
    GetCommand(jumpOut1).offs = outOfBranch;
    ///
    PushCommand({DEC_REG0, 0}, __FILE__, __LINE__);
    PushCommand({JUMP_IF_NON_ZERO, loop}, __FILE__, __LINE__);
    
    PushCommand({RET, 0}, __FILE__, __LINE__);
}

esint32 VRenderSystem::PushDefaultMainFunction()
{
    
    PushRenderShadowFunction();
    const esint32 MainRendererChain = 0;
    const esint32 NumLights = 1;
    const esint32 StackPointer = 2;
    esint32 ret =
    PushCommand({MOV_IMME_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_SP, 0}, __FILE__, __LINE__);
    PushCommand({ALLOC_IMME, 8}, __FILE__, __LINE__);
    
    PushCommand({GET_MAIN_RDR_CHN_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, MainRendererChain}, __FILE__, __LINE__);
    
    PushCommand({GET_NUM_FWD_KEY_LIGHTS_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, NumLights}, __FILE__, __LINE__);
    
    PushCommand({MOV_REG0_TO_REG1, 0}, __FILE__, __LINE__);
    PushCommand({MOV_IMME_TO_REG2, 0}, __FILE__, __LINE__);
    PushCommand({SUB_REG0_ASS_REG1_REG2, 0}, __FILE__, __LINE__);
    
    esint32 gotoRenderMainRendererChain =
    PushCommand({JUMP_IF_ZERO, 0}, __FILE__, __LINE__); /// if (NumLights == 0) goto startRenderMainRendererChain;
    
    PushCommand({MOV_SP_TO_REG0, 0}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_MEM, StackPointer}, __FILE__, __LINE__);
    
    PushCommand({PUSH_FWD_KEY_LIGHTS, 0}, __FILE__, __LINE__);
    PushCommand({PUSH, NumLights}, __FILE__, __LINE__);
    
    PushCommand({ICALL, 0}, __FILE__, __LINE__);
    
    PushCommand({MOV_MEM_TO_REG0, StackPointer}, __FILE__, __LINE__);
    PushCommand({MOV_REG0_TO_SP, 0}, __FILE__, __LINE__);
    
    ///PushCommand({PRINT_STATUS, 0});
    
    euint32 startRenderMainRendererChain =
    PushCommand({RENDER, MainRendererChain}, __FILE__, __LINE__);
    PushCommand({FINISH, 0}, __FILE__, __LINE__);
    
    GetCommand(gotoRenderMainRendererChain).offs = startRenderMainRendererChain;
    
    m_entryPoint = ret;
    return ret;
}

int VRenderSystem::Render()
{
    {
        VLightManagerInstance inst = m_forwardLightManager->GetInstance();
        inst->Update();
    }
    SetProgramCounter(m_entryPoint);
    Run();
    return 0;
}

void VRenderSystem::ResetFrame(int x, int y, int width, int height)
{
    m_mainRendererChain->Resize(width, height);
}

VRendererBasePtr VRenderSystem::GetRenderer(const xhn::static_string rendererName)
{
    return m_mainRendererChain->GetRenderer(rendererName);
}

VViewportPtr VRenderSystem::GetViewport()
{
    return m_mainRendererChain->GetCurrentViewport();
}

VCameraPtr VRenderSystem::GetCamera()
{
    return m_mainRendererChain->GetCurrentCamera();
}

VTexture2DPtr VRenderSystem::RegisterNamedInternalTexture2D(const xhn::static_string texName,
                                                            PixelFormat pixelFormat,
                                                            euint32 width,
                                                            euint32 height)
{
    VTexture2DPtr ret =
    VTexture2DGallery::Get(this)->RegisterInternalTexture(texName);
    VResourceGroup* grp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
    VTexture2DResource* res = VNEW VTexture2DResource(this, grp, ret);
    grp->AddResource(texName, res);
    ret->CreateEmptyTextureNoBuffered(pixelFormat, width, height);
    return ret;
}
VTextureCubePtr VRenderSystem::RegisterNamedInternalTextureCube(const xhn::static_string texName,
                                                                PixelFormat pixelFormat,
                                                                euint32 width,
                                                                euint32 height)
{
    VTextureCubePtr ret =
    VTextureCubeGallery::Get(this)->RegisterInternalTexture(texName);
    VResourceGroup* grp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
    VTextureCubeResource* res = VNEW VTextureCubeResource(this, grp, ret);
    grp->AddResource(texName, res);
    ret->CreateEmptyTextureNoBuffered(pixelFormat, width, height);
    return ret;
}

///==========================================================================///
///  渲染系统渲染                                                              ///
///==========================================================================///

void VRenderSystem::BeginRender()
{
    FrameBufferManager::Get(this)->Update();
    m_BaseFrameBuffer = FrameBufferManager::Get(this)->MarkCurrentFramebufferAsBinding();
    VRobotManager* robotManager = VRobotManager::Get(this);
    if (robotManager->GetDispatchIntensity() == VRobotManager::Strong) {
        robotManager->DispatchAllRobots();
    }
}
void VRenderSystem::EndRender()
{
}

///==========================================================================///
///  注册顶点声明到全局顶点声明表中                                               ///
///==========================================================================///

VVertexDeclaration* VRenderSystem::RegisterVertexDeclaration(VVertexDeclaration& dec)
{
    xhn::SpinLock::Instance inst = m_render_system_lock.Lock();
    
    VertexDeclSet::iterator iter = m_vtx_dec_set->find(&dec);
    if (iter != m_vtx_dec_set->end()) {
        return *iter;
    }
    else {
        VVertexDeclaration* ret = dec.Clone();
        m_vtx_dec_set->insert(ret);
        return ret;
    }
}

///==========================================================================///
///  注册pass到全局pass表中                                                    ///
///==========================================================================///

VPassPtr VRenderSystem::RegisterCompositorPass(CompPassDecl dec)
{
    xhn::SpinLock::Instance inst = m_render_system_lock.Lock();
    
    CompPassDeclToPassMap::iterator iter = m_compositor_pass_map->find(dec);
    if (iter != m_compositor_pass_map->end()) {
        return iter->second;
    }
    else {
        CompPassDecl tmp = CompPassDecl_clone(dec);
        VPassPtr ret = create_compositor_pass(this, tmp->dec, tmp->mode, tmp->flip_flags, tmp->using_fxaa);
        m_compositor_pass_map->insert(xhn::make_pair(tmp, ret));
        return ret;
    }
}

VTexture2DPtr _default_texture(VRenderSystem* renderSys)
{
    VResourceGroup* resGrp = VResourceSystem::Get(renderSys)->GetResourceGroup(TextureGroupName);
    VResourcePtr res = resGrp->_Load(DefaultTexture2DDetector::DefaultTexture2DName);
    VTexture2DResource* tex_res = res->DynamicCast<VTexture2DResource>();
    VTexture2DPtr tex = tex_res->GetTexture();
    return tex;
}

VTextureCubePtr _default_texture_cube(VRenderSystem* renderSys)
{
    VResourceGroup* resGrp = VResourceSystem::Get(renderSys)->GetResourceGroup(TextureGroupName);
    VResourcePtr res = resGrp->_Load(DefaultTextureCubeDetector::DefaultTextureCubeName);
    VTextureCubeResource* tex_res = res->DynamicCast<VTextureCubeResource>();
    VTextureCubePtr tex = tex_res->GetTexture();
    return tex;
}

///==========================================================================///
///  创建和载入2d纹理                                                           ///
///==========================================================================///

VTexture2DPtr VRenderSystem::NewTexture2d(const xhn::static_string filename,
                                          const xhn::static_string res_group)
{
	VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(res_group);
    try {
        VResourcePtr res = resGrp->_New(filename);
        VTexture2DResource* tex_res = res->DynamicCast<VTexture2DResource>();
		VTexture2DPtr tex = tex_res->GetTexture();
		return tex;
    }
	catch (NewResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    return _default_texture(this);
}

VTexture2DPtr VRenderSystem::GetTexture2d(const xhn::static_string filename,
                                          bool loadDefaultTex)
{
    xhn::static_string resType = VResourceSystem::Get(this)->DetectResourceType(filename);
    if (resType == VTexture2DDetector::Texture2DType || resType == DefaultTexture2DDetector::DefaultTexture2DType)
    {
        VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(TextureGroupName);
        try {
            VTexture2DResource* texRes = resGrp->_Load(filename)->DynamicCast<VTexture2DResource>();
            return texRes->m_tex;
        }
        catch (LoadResourceException& e) {
            ///show_information_dialog(e.what());
            elog("Error:%s", e.what());
        }
        return _default_texture(this);
    }
    else if (resType == InternalTexture2DDetector::InternalTexture2DType)
    {
        VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
        try {
            VTexture2DResource* texRes = resGrp->_Load(filename)->DynamicCast<VTexture2DResource>();
            return texRes->m_tex;
        }
        catch (LoadResourceException& e) {
            ///show_information_dialog(e.what());
            elog("Error:%s", e.what());
        }
        return _default_texture(this);
    }
    else
    {
        if (loadDefaultTex) {
            return _default_texture(this);
        }
        else {
            return nullptr;
        }
    }
}

///==========================================================================///
///  创建和载入cube纹理                                                        ///
///==========================================================================///

VTextureCubePtr VRenderSystem::NewTextureCube(const xhn::static_string filename,
                                              const xhn::static_string res_group)
{
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(res_group);
    try {
        VResourcePtr res = resGrp->_New(filename);
        VTextureCubeResource* tex_res = res->DynamicCast<VTextureCubeResource>();
        VTextureCubePtr tex = tex_res->GetTexture();
        return tex;
    }
    catch (NewResourceException& e) {
        elog("Error:%s", e.what());
    }
    return _default_texture_cube(this);
}
VTextureCubePtr VRenderSystem::GetTextureCube(const xhn::static_string filename,
                                              bool loadDefaultTex)
{
    xhn::static_string resType = VResourceSystem::Get(this)->DetectResourceType(filename);
    if (resType == VTextureCubeDetector::TextureCubeType || resType == DefaultTextureCubeDetector::DefaultTextureCubeType)
    {
        VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(TextureGroupName);
        try {
            VTextureCubeResource* texRes = resGrp->_Load(filename)->DynamicCast<VTextureCubeResource>();
            return texRes->m_tex;
        }
        catch (LoadResourceException& e) {
            elog("Error:%s", e.what());
        }
        return _default_texture_cube(this);
    }
    else if (resType == InternalTextureCubeDetector::InternalTextureCubeType)
    {
        VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(InternalTextureGroupName);
        try {
            VTextureCubeResource* texRes = resGrp->_Load(filename)->DynamicCast<VTextureCubeResource>();
            return texRes->m_tex;
        }
        catch (LoadResourceException& e) {
            elog("Error:%s", e.what());
        }
        return _default_texture_cube(this);
    }
    else
    {
        if (loadDefaultTex) {
            return _default_texture_cube(this);
        }
        else {
            return nullptr;
        }
    }
}

///==========================================================================///
///  创建和载入gui配置                                                         ///
///==========================================================================///

VXMLResourcePtr VRenderSystem::NewGuiConfig(const xhn::static_string filename)
{
	VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup("GUIConfig");
    try {
        VResourcePtr res = resGrp->_New(filename);
        VXMLResourcePtr ret(res->DynamicCast<VXMLResource>());
        return ret;
    }
	catch (NewResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: xml未实现默认资源
    return NULL;
}

VXMLResourcePtr VRenderSystem::LoadGuiConfig(const xhn::static_string filename)
{
	VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup("GUIConfig");
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VXMLResourcePtr ret(res->DynamicCast<VXMLResource>());
        return ret;
    }
	catch (LoadResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: xml未实现默认资源
    return NULL;
}

///==========================================================================///
///  创建和载入动画配置                                                         ///
///==========================================================================///

VXMLResourcePtr VRenderSystem::NewAnimationConfig(const xhn::static_string filename)
{
	VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup("AnimationConfig");
    try {
        VResourcePtr res = resGrp->_New(filename);
        VXMLResourcePtr ret(res->DynamicCast<VXMLResource>());
        return ret;
    }
	catch (NewResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: xml未实现默认资源
    return NULL;
}

VXMLResourcePtr VRenderSystem::LoadAnimationConfig(const xhn::static_string filename)
{
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup("AnimationConfig");
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VXMLResourcePtr ret(res->DynamicCast<VXMLResource>());
        return ret;
    }
	catch (LoadResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: xml未实现默认资源
    return NULL;
}

///==========================================================================///
///  载入材质原型和实例                                                         ///
///==========================================================================///

VMaterialPrototypePtr VRenderSystem::LoadMaterialPrototype(const xhn::static_string filename)
{
    VPerformanceMeasurementPtr pm;
    if (m_log_level & PERFORMANCE_LOG) {
        pm = VNEW VPerformanceMeasurement("LoadMaterialPrototype");
    }
    
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(MaterialPrototypeGroupName);
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VMaterialPrototypeResourcePtr ret(res->DynamicCast<VMaterialPrototypeResource>());
        return ret->GetMaterialPrototype();
    }
    catch (LoadResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: material prototype未实现默认资源
    return NULL;
}

VMaterialInstancePtr VRenderSystem::LoadMaterialInstance(const xhn::static_string filename)
{
    VPerformanceMeasurementPtr pm;
    if (m_log_level & PERFORMANCE_LOG) {
        pm = VNEW VPerformanceMeasurement("LoadMaterialInstance");
    }
    
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(MaterialInstanceGroupName);
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VMaterialInstanceResourcePtr ret(res->DynamicCast<VMaterialInstanceResource>());
        return ret->GetMaterialInstance();
    }
    catch (LoadResourceException& e) {
        ///show_information_dialog(e.what());
        elog("Error:%s", e.what());
    }
    /// ToDo: material instance未实现默认资源
    return nullptr;
}

VSkinResourcePtr VRenderSystem::LoadSkin(const xhn::static_string filename)
{
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(SkinGroupName);
    
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VSkinResourcePtr ret(res->DynamicCast<VSkinResource>());
        return ret;
    }
    catch (LoadResourceException& e) {
        elog("Error:%s", e.what());
    }
    /// ToDo: skin未实现默认资源
    return nullptr;
}
VAnimationPtr VRenderSystem::LoadAnimation(const xhn::static_string filename)
{
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(AnimationGroupName);
    
    try {
        VResourcePtr res = resGrp->_Load(filename);
        VAnimationResourcePtr ret(res->DynamicCast<VAnimationResource>());
        return ret->GetAnimation();
    }
    catch (LoadResourceException& e) {
        elog("Error:%s", e.what());
    }
    /// ToDo: animation未实现默认资源
    return nullptr;
}
VResourcePtr VRenderSystem::LoadResource(const xhn::static_string filename,
                                         const xhn::static_string resourceGroup)
{
    VResourceGroup* resGrp = VResourceSystem::Get(this)->GetResourceGroup(resourceGroup);
    
    try {
        VResourcePtr res = resGrp->_Load(filename);
        return res;
    }
    catch (LoadResourceException& e) {
        elog("Error:%s", e.what());
    }
    return nullptr;
}

VVertexBuffer* VRenderSystem::AllocVertexBuffer(VVertexDeclaration* vertexDeclaration)
{
	return m_render_buffer_manager->AllocVertexBuffer(vertexDeclaration);
}
VIndexBuffer* VRenderSystem::AllocIndexBuffer()
{
	return m_render_buffer_manager->AllocIndexBuffer();
}
void VRenderSystem::FreeVertexBuffer(VVertexBuffer* buf)
{
	m_render_buffer_manager->FreeVertexBuffer(buf);
}
void VRenderSystem::FreeIndexBuffer(VIndexBuffer* buf)
{
	m_render_buffer_manager->FreeIndexBuffer(buf);
}

void VRenderSystem::RegisterResourceGroup(const xhn::static_string groupName,
                                          const xhn::static_string parentGroupName)
{
    VResourceSystem::Get(this)->NewResourceGroup(groupName, parentGroupName, Public);
}

VResourceGroup* VRenderSystem::GetResourceGroup(const xhn::static_string groupName)
{
    return VResourceSystem::Get(this)->GetResourceGroup(groupName);
}

MSDebuggerObj* VRenderSystem::GetMaterialDebugger()
{
    return &m_msDebugger;
}

euint32 VRenderSystem::GetMaxJointMatrices()
{
    return 50;
}
}