import streamlit as st
import ezdxf
import math
import io
import base64
from ezdxf.enums import TextEntityAlignment
from ezdxf.fonts.fonts import find_font_face, FontFace
from ezdxf.addons.text2path import make_hatches_from_str
from ezdxf.tools import pattern
from ezdxf.entities import LWPolyline, Polyline, Circle, DXFGraphic, Hatch
from ezdxf.addons.drawing import RenderContext, Frontend
from ezdxf.addons.drawing.properties import LayoutProperties, Properties
from ezdxf.addons.drawing.matplotlib import MatplotlibBackend
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.figure import Figure
import tempfile
import os

# Configure Streamlit page
st.set_page_config(
    page_title="DXF Hatch Generator",
    page_icon="🔧",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Pre-defined PAT patterns
PREDEFINED_PATTERNS = """
*ANSI31, ANSI Iron, Brick, Stone masonry
45, 0,0, 0.176776695,0.176776695, 0.125,-0.051776695

*ANSI32, ANSI Steel
45, 0,0, 0.088388348,0.088388348, 0.0625,-0.025

*ANSI33, ANSI Aluminum
45, 0,0, 0.0625,0.0625, 0.04375,-0.01875

*ANSI34, ANSI Copper
45, 0,0, 0.044194174,0.044194174, 0.03125,-0.013

*LINE, Parallel horizontal lines
0, 0,0, 0,0.125

*CROSS, Crosshatch
0, 0,0, 0.125,0.125
90, 0,0, 0.125,0.125

*BRICK, Brick wall pattern
0, 0,0, 0.25,0.125, 0.25,-0.25
90, 0,0, 0.125,0.25

*DOTS, Dot Grid
0, 0,0, 0.25,0.25, 0,-0.125

*GRID, Square Grid
0, 0,0, 0.25,0.25
90, 0,0, 0.25,0.25

*OUTLINE_SQUARE_GRID, Outlined 0.5x0.5 squares, 0.2 spacing
0, 0,0,   0,0.7, 0.5,-0.2
0, 0,0.5, 0,0.7, 0.5,-0.2
90, 0,0,   0,0.7, 0.5,-0.2
90, 0.5,0, 0,0.7, 0.5,-0.2
"""

class ImprovedHatchFrontend(Frontend):
    def __init__(self, ctx: RenderContext, out: MatplotlibBackend, hatch_color: str = "#000000", boundary_color: str = "#FFFFFF"):
        super().__init__(ctx, out)
        self.hatch_color = hatch_color
        self.boundary_color = boundary_color
        
    def override_properties(self, entity: DXFGraphic, properties: Properties) -> None:
        if isinstance(entity, Hatch):
            properties.color = self.hatch_color
            properties.lineweight = 0.5
        else:
            properties.color = self.boundary_color
            if hasattr(properties, 'lineweight'):
                properties.lineweight = 0.3

def load_predefined_patterns():
    """Load predefined patterns"""
    try:
        return pattern.parse(PREDEFINED_PATTERNS)
    except Exception as e:
        st.error(f"Could not load pre-defined patterns: {e}")
        return {}

def color_to_dxf_index(color_hex):
    """Convert hex color to DXF color index"""
    # Remove # if present
    color_hex = color_hex.lstrip('#')
    # Convert to RGB
    r = int(color_hex[0:2], 16)
    g = int(color_hex[2:4], 16)
    b = int(color_hex[4:6], 16)
    
    # Simple color mapping to DXF indices
    if r > 200 and g < 100 and b < 100: return 1  # Red
    elif r > 200 and g > 200 and b < 100: return 2  # Yellow
    elif r < 100 and g > 200 and b < 100: return 3  # Green
    elif r < 100 and g > 200 and b > 200: return 4  # Cyan
    elif r < 100 and g < 100 and b > 200: return 5  # Blue
    elif r > 200 and g < 100 and b > 200: return 6  # Magenta
    elif (r + g + b) / 3 > 200: return 7  # White
    else: return 0  # Black/ByBlock

def get_entity_points(entity, resolution=0.05):
    """Extract points from various entity types"""
    def to_2d(point):
        if hasattr(point, '__len__') and len(point) >= 2:
            return (float(point[0]), float(point[1]))
        return point

    try:
        if entity.dxftype() == "CIRCLE":
            center = entity.dxf.center
            radius = entity.dxf.radius
            if radius <= 0: return []
            num_points = max(16, int(2 * math.pi * radius / max(resolution, 0.001)))
            points = []
            for i in range(num_points):
                angle = (2 * math.pi * i) / num_points
                x = center[0] + radius * math.cos(angle)
                y = center[1] + radius * math.sin(angle)
                points.append((x, y))
            return points
        elif entity.dxftype() == "ELLIPSE":
            return [to_2d(p) for p in entity.flattening(resolution)]
        elif entity.dxftype() == "LWPOLYLINE":
            return [to_2d(p) for p in entity.get_points()]
        elif entity.dxftype() == "POLYLINE":
            return [to_2d(vertex.dxf.location) for vertex in entity.vertices]
    except Exception as e:
        st.warning(f"Error converting {entity.dxftype()} to points: {e}")
    return []

def calculate_area(points):
    """Calculate area of polygon using shoelace formula"""
    if len(points) < 3: return 0
    area, n = 0, len(points)
    for i in range(n):
        j = (i + 1) % n
        area += points[i][0] * points[j][1]
        area -= points[j][0] * points[i][1]
    return abs(area) / 2.0

def analyze_dxf_file(doc):
    """Analyze DXF file and return statistics"""
    if not doc: return None
    
    msp = doc.modelspace()
    total_entities = len(msp)
    potential_boundaries = 0
    entity_counts = {}
    layers = set()
    
    for entity in msp:
        entity_type = entity.dxftype()
        entity_counts[entity_type] = entity_counts.get(entity_type, 0) + 1
        layers.add(entity.dxf.layer)
        
        if ((entity_type == "LWPOLYLINE" and hasattr(entity, 'is_closed') and entity.is_closed) or
            (entity_type == "POLYLINE" and hasattr(entity, 'is_closed') and entity.is_closed) or
            (entity_type == "CIRCLE") or (entity_type == "ELLIPSE")):
            potential_boundaries += 1
    
    return {
        'total_entities': total_entities,
        'potential_boundaries': potential_boundaries,
        'layers': sorted(list(layers)),
        'entity_counts': entity_counts
    }

def get_boundary_entities(doc, detect_settings, selected_layer="All Layers"):
    """Get boundary entities based on detection settings"""
    if not doc: return []
    
    msp = doc.modelspace()
    boundaries = []
    
    for entity in msp:
        if selected_layer != "All Layers" and entity.dxf.layer != selected_layer:
            continue
            
        entity_type = entity.dxftype()
        
        if ((entity_type == "LWPOLYLINE" and detect_settings['lwpolyline'] and 
             hasattr(entity, 'is_closed') and entity.is_closed) or
            (entity_type == "POLYLINE" and detect_settings['polyline'] and 
             hasattr(entity, 'is_closed') and entity.is_closed) or
            (entity_type == "CIRCLE" and detect_settings['circle']) or
            (detect_settings['other'] and entity_type in ["ELLIPSE", "SPLINE"])):
            boundaries.append(entity)
    
    return boundaries

def create_hatch_document(mode, text_settings=None, dxf_doc=None, detect_settings=None, 
                         layer_filter="All Layers", hatch_props=None, show_boundaries=True):
    """Create DXF document with hatch"""
    if not hatch_props:
        return None
        
    pattern_name, pattern_def, scale, angle, hatch_color, boundary_color = hatch_props
    
    try:
        if mode == 'text' and text_settings:
            text, font_name, font_height = text_settings
            if not text:
                return None
                
            doc = ezdxf.new()
            msp = doc.modelspace()
            
            try:
                font_face = find_font_face(font_name)
            except:
                font_face = FontFace()
                
            hatches = make_hatches_from_str(text, font_face, size=font_height)
            for h in hatches:
                h.set_pattern_fill(name=pattern_name, scale=scale, angle=angle, definition=pattern_def)
                h.dxf.color = color_to_dxf_index(hatch_color)
                msp.add_entity(h)
                
            return doc
            
        elif mode == 'dxf' and dxf_doc:
            out_doc = ezdxf.new()
            out_msp = out_doc.modelspace()
            
            # Add boundaries if requested
            if show_boundaries:
                for entity in dxf_doc.modelspace():
                    try:
                        entity_copy = entity.copy()
                        entity_copy.dxf.color = color_to_dxf_index(boundary_color)
                        out_msp.add_entity(entity_copy)
                    except Exception as e:
                        st.warning(f"Error copying entity: {e}")
            
            # Add hatch
            candidate_entities = get_boundary_entities(dxf_doc, detect_settings, layer_filter)
            all_shapes = []
            
            for entity in candidate_entities:
                points = get_entity_points(entity)
                if len(points) >= 3:
                    area = calculate_area(points)
                    all_shapes.append({'entity': entity, 'points': points, 'area': area})
            
            if all_shapes:
                # Sort by area (largest first)
                all_shapes.sort(key=lambda x: x['area'], reverse=True)
                
                # Create hatch
                hatch = out_msp.add_hatch(color=color_to_dxf_index(hatch_color))
                hatch.set_pattern_fill(name=pattern_name, scale=scale, angle=angle, definition=pattern_def)
                
                # Add outer boundary
                outer_shape = all_shapes[0]
                hatch.paths.add_polyline_path(outer_shape['points'], is_closed=True)
                
                # Add inner boundaries (holes)
                inner_threshold = outer_shape['area'] * 0.8
                inner_shapes = [s for s in all_shapes[1:] if s['area'] < inner_threshold]
                
                for shape in inner_shapes:
                    hatch.paths.add_polyline_path(shape['points'], is_closed=True)
            
            return out_doc
            
    except Exception as e:
        st.error(f"Error creating hatch document: {e}")
        return None

def render_dxf_preview(doc, hatch_color="#000000", boundary_color="#FFFFFF"):
    """Render DXF document to matplotlib figure"""
    if not doc or not doc.modelspace():
        return None
        
    try:
        fig, ax = plt.subplots(figsize=(12, 8))
        ax.set_aspect('equal')
        ax.grid(True, alpha=0.3)
        ax.axhline(0, color='red', linestyle='--', alpha=0.5)
        ax.axvline(0, color='red', linestyle='--', alpha=0.5)
        
        msp = doc.modelspace()
        ctx = RenderContext(doc)
        msp_props = LayoutProperties.from_layout(msp)
        msp_props.set_colors(boundary_color)
        
        out = MatplotlibBackend(ax)
        frontend = ImprovedHatchFrontend(ctx, out, hatch_color=hatch_color, boundary_color=boundary_color)
        frontend.draw_layout(msp, finalize=True, layout_properties=msp_props)
        
        plt.tight_layout()
        return fig
        
    except Exception as e:
        st.error(f"Error rendering DXF: {e}")
        return None

def save_dxf_to_bytes(doc):
    """Save DXF document to bytes for download"""
    if not doc:
        return None
        
    try:
        # Method 1: Use BytesIO for in-memory operations
        try:
            # Create a temporary file with delete=False first
            with tempfile.NamedTemporaryFile(suffix='.dxf', delete=False) as tmp_file:
                tmp_path = tmp_file.name
            
            # Save DXF to the file
            doc.saveas(tmp_path)
            
            # Read the file content
            with open(tmp_path, 'rb') as f:
                dxf_bytes = f.read()
            
            # Clean up - try multiple times if needed
            for attempt in range(3):
                try:
                    os.unlink(tmp_path)
                    break
                except (PermissionError, FileNotFoundError):
                    if attempt == 2:  # Last attempt
                        pass  # Ignore if we can't delete
                    else:
                        import time
                        time.sleep(0.1)  # Wait a bit and try again
            
            return dxf_bytes
            
        except Exception as temp_error:
            # Method 2: Fallback - use unique filename
            import uuid
            import time
            unique_filename = f"temp_dxf_{uuid.uuid4().hex}_{int(time.time())}.dxf"
            temp_dir = tempfile.gettempdir()
            tmp_path = os.path.join(temp_dir, unique_filename)
            
            try:
                doc.saveas(tmp_path)
                
                with open(tmp_path, 'rb') as f:
                    dxf_bytes = f.read()
                
                # Try to clean up, but don't fail if we can't
                try:
                    os.unlink(tmp_path)
                except:
                    pass
                
                return dxf_bytes
                
            except Exception as fallback_error:
                st.error(f"Error saving DXF (fallback method): {fallback_error}")
                return None
                
    except Exception as e:
        st.error(f"Error saving DXF: {e}")
        return None

# Initialize session state
if 'loaded_patterns' not in st.session_state:
    st.session_state.loaded_patterns = load_predefined_patterns()

if 'imported_dxf_doc' not in st.session_state:
    st.session_state.imported_dxf_doc = None

if 'generation_mode' not in st.session_state:
    st.session_state.generation_mode = 'text'

if 'current_doc' not in st.session_state:
    st.session_state.current_doc = None

# Main UI
st.title("DXF Hatch Generator")
st.markdown("**Real-time preview** - Generate DXF files with hatch patterns from text or import existing DXF boundaries")

# Create main layout
col1, col2 = st.columns([3, 1])

with col1:
    st.header("🔍 Preview")
    preview_container = st.container()

with col2:
    st.header("💾 Export")
    export_container = st.container()

# Sidebar for settings
with st.sidebar:
    st.header("⚙️ Settings")
    
    # Generation mode
    mode = st.radio("Generation Mode", ["Text to Hatch", "Import DXF Boundary"], index=0)
    st.session_state.generation_mode = 'text' if mode == "Text to Hatch" else 'dxf'
    
    # Text Settings (only show in text mode)
    text_input = None
    font_name = None
    font_height = None
    
    if st.session_state.generation_mode == 'text':
        st.subheader("📝 Generate from Text")
        text_input = st.text_input("Text", "TEXT", key="text_input")
        font_name = st.selectbox("Font", ["Arial", "Times New Roman", "Courier New", "Calibri", "Verdana"], key="font_name")
        font_height = st.number_input("Font Height", min_value=1.0, max_value=1000.0, value=10.0, step=0.5, key="font_height")
        st.markdown("---")
    
    # DXF Import Section
    selected_layer = "All Layers"
    detect_lwpolyline = True
    detect_polyline = True
    detect_circle = True
    detect_other = True
    
    if st.session_state.generation_mode == 'dxf':
        st.subheader("📁 Import DXF Boundary")
        uploaded_file = st.file_uploader("Choose DXF file", type=['dxf'])
        
        if uploaded_file is not None:
            try:
                # Save uploaded file temporarily
                with tempfile.NamedTemporaryFile(suffix='.dxf', delete=False) as tmp_file:
                    tmp_file.write(uploaded_file.read())
                    tmp_file_path = tmp_file.name
                
                # Read DXF file
                st.session_state.imported_dxf_doc = ezdxf.readfile(tmp_file_path)
                os.unlink(tmp_file_path)
                
                # Analyze file
                analysis = analyze_dxf_file(st.session_state.imported_dxf_doc)
                if analysis:
                    st.success(f"✅ DXF loaded successfully!")
                    st.write(f"**Total Entities:** {analysis['total_entities']}")
                    st.write(f"**Potential Boundaries:** {analysis['potential_boundaries']}")
                    st.write(f"**Layers:** {len(analysis['layers'])}")
                    
                    # Entity types
                    with st.expander("Entity Types"):
                        for entity_type, count in sorted(analysis['entity_counts'].items()):
                            st.write(f"• {entity_type}: {count}")
                    
                    # Layer filter
                    st.subheader("🎯 Layer Filter")
                    layer_options = ["All Layers"] + analysis['layers']
                    selected_layer = st.selectbox("Select Layer", layer_options, key="layer_filter")
                    
                    # Boundary detection
                    st.subheader("🔍 Boundary Detection")
                    detect_lwpolyline = st.checkbox("Detect LWPOLYLINE (closed)", True, key="detect_lwpolyline")
                    detect_polyline = st.checkbox("Detect POLYLINE (closed)", True, key="detect_polyline")
                    detect_circle = st.checkbox("Detect CIRCLE", True, key="detect_circle")
                    detect_other = st.checkbox("Detect ELLIPSE & other", True, key="detect_other")
                    
            except Exception as e:
                st.error(f"❌ Error reading DXF file: {e}")
                st.session_state.imported_dxf_doc = None
        else:
            st.session_state.imported_dxf_doc = None
        
        st.markdown("---")
    
    # Hatch Properties - Always visible
    st.subheader("🎨 Hatch Properties")
    
    selected_pattern = None
    scale = 1.0
    angle = 0.0
    boundary_color = "#000000"
    hatch_color = "#FFFFFF"
    show_boundaries = True
    
    if st.session_state.loaded_patterns:
        pattern_names = list(st.session_state.loaded_patterns.keys())
        selected_pattern = st.selectbox("Pattern", pattern_names, key="pattern_select")
        
        scale = st.number_input("Scale", min_value=0.01, max_value=1000.0, value=1.0, step=0.1, key="scale_input")
        angle = st.number_input("Angle (degrees)", min_value=-360.0, max_value=360.0, value=0.0, step=15.0, key="angle_input")
        
        # Colors
        st.subheader("🎨 Colors")
        boundary_color = st.color_picker("Boundary Color", "#FFFFFF", key="boundary_color")
        hatch_color = st.color_picker("Hatch Color", "#000000", key="hatch_color")
        
        # Export options
        st.subheader("💾 Export Options")
        show_boundaries = st.checkbox("Keep Boundaries in Export", True, key="show_boundaries")
    
    st.markdown("---")
    
    # Import custom PAT file
    st.subheader("📂 Custom Patterns")
    pat_file = st.file_uploader("Import .pat file", type=['pat'])
    if pat_file is not None:
        try:
            pat_content = pat_file.read().decode('utf-8')
            new_patterns = pattern.parse(pat_content)
            if new_patterns:
                added_count = 0
                for name, definition in new_patterns.items():
                    if name not in st.session_state.loaded_patterns:
                        st.session_state.loaded_patterns[name] = definition
                        added_count += 1
                if added_count > 0:
                    st.success(f"✅ Added {added_count} new pattern(s)")
                    st.rerun()
                else:
                    st.info("ℹ️ All patterns from the file were already loaded.")
            else:
                st.warning("⚠️ No valid patterns found in file")
        except Exception as e:
            st.error(f"❌ Error reading PAT file: {e}")

# Real-time preview generation
current_doc = None

if st.session_state.loaded_patterns and selected_pattern:
    pattern_def = st.session_state.loaded_patterns[selected_pattern]
    hatch_props = (selected_pattern, pattern_def, scale, angle, hatch_color, boundary_color)
    
    if st.session_state.generation_mode == 'text':
        if text_input:
            text_settings = (text_input, font_name, font_height)
            current_doc = create_hatch_document('text', text_settings=text_settings, hatch_props=hatch_props)
            
    elif st.session_state.generation_mode == 'dxf':
        if st.session_state.imported_dxf_doc:
            detect_settings = {
                'lwpolyline': detect_lwpolyline,
                'polyline': detect_polyline,
                'circle': detect_circle,
                'other': detect_other
            }
            
            current_doc = create_hatch_document('dxf', dxf_doc=st.session_state.imported_dxf_doc,
                                              detect_settings=detect_settings, layer_filter=selected_layer,
                                              hatch_props=hatch_props, show_boundaries=show_boundaries)

# Store current document for export
st.session_state.current_doc = current_doc

# Display preview
with preview_container:
    if current_doc:
        try:
            fig = render_dxf_preview(current_doc, hatch_color, boundary_color)
            if fig:
                st.pyplot(fig, use_container_width=True)
                plt.close(fig)
            else:
                st.warning("⚠️ Could not render preview")
        except Exception as e:
            st.error(f"❌ Preview error: {e}")
    else:
        # Show placeholder or instructions
        if st.session_state.generation_mode == 'text':
            if not text_input:
                st.info("ℹ️ Enter text to see preview")
            else:
                st.info("ℹ️ Adjust settings to generate preview")
        else:
            if not st.session_state.imported_dxf_doc:
                st.info("ℹ️ Upload a DXF file to see preview")
            else:
                st.info("ℹ️ Adjust settings to generate preview")

# Export section
with export_container:
    if current_doc:
        dxf_bytes = save_dxf_to_bytes(current_doc)
        
        if dxf_bytes:
            filename = "hatch_output.dxf"
            if st.session_state.generation_mode == 'text' and text_input:
                safe_text = "".join(c for c in text_input if c.isalnum() or c in (' ', '-', '_')).rstrip()
                filename = f"{safe_text.replace(' ', '_')}_hatch.dxf"
            
            st.download_button(
                label="📥 Download DXF",
                data=dxf_bytes,
                file_name=filename,
                mime="application/octet-stream",
                type="primary",
                use_container_width=True
            )
            
            st.success("✅ Ready for download!")
            
            # Show file info
            file_size = len(dxf_bytes)
            if file_size < 1024:
                size_str = f"{file_size} bytes"
            elif file_size < 1024 * 1024:
                size_str = f"{file_size / 1024:.1f} KB"
            else:
                size_str = f"{file_size / (1024 * 1024):.1f} MB"
            
            st.caption(f"File size: {size_str}")
        else:
            st.error("❌ Could not prepare file for download")
    else:
        st.info("ℹ️ Configure settings to enable download")
    
    st.markdown("---")
    
    # Instructions
    st.subheader("📖 Quick Guide")
    
    if st.session_state.generation_mode == 'text':
        st.markdown("""
        **Text Mode:**
        1. 📝 Enter your text
        2. 🔤 Choose font and size  
        3. 🎨 Select hatch pattern
        4. ⚙️ Adjust scale/angle/colors
        5. 🔍 Preview updates automatically
        6. 💾 Download when ready
        """)
    else:
        st.markdown("""
        **DXF Import Mode:**
        1. 📁 Upload DXF with boundaries
        2. 🎯 Configure detection settings
        3. 🎨 Select hatch pattern
        4. ⚙️ Adjust properties
        5. 🔍 Preview updates automatically  
        6. 💾 Download when ready
        """)
    
    st.markdown("""
    **💡 Tips:**
    - Preview updates in real-time
    - Use appropriate scale for your drawing
    - Import custom .pat files for more patterns
    - Toggle boundary visibility for export
    """)

# Footer
st.markdown("---")
st.markdown("**DXF Hatch Generator** - Real-time preview | Convert text or boundaries to hatched DXF files")













